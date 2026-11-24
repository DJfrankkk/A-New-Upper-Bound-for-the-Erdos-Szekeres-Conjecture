import ESVerify.Planar

/-! The union of a cap and a cup with common endpoints, as used in
Proposition 4.2. A supporting line at each vertex also supports the union,
because the other chain lies on the opposite side of the common chord. -/

set_option autoImplicit false

namespace ESVerify

private noncomputable def chordY (a b : Point) (x : ℝ) : ℝ :=
  (1 - (x - a.1) / (b.1 - a.1)) * a.2 + ((x - a.1) / (b.1 - a.1)) * b.2

private theorem supportValue_chord (cap : Bool) (m : ℝ) (a b : Point) (x : ℝ)
    (hab : a.1 < b.1) :
    supportValue cap m (x, chordY a b x) =
      (1 - (x - a.1) / (b.1 - a.1)) * supportValue cap m a +
      ((x - a.1) / (b.1 - a.1)) * supportValue cap m b := by
  have hden := ne_of_gt (sub_pos.mpr hab)
  have hx : (1 - (x - a.1) / (b.1 - a.1)) * a.1 +
      ((x - a.1) / (b.1 - a.1)) * b.1 = x := by
    calc
      _ = a.1 + ((x - a.1) / (b.1 - a.1)) * (b.1 - a.1) := by ring
      _ = x := by rw [div_mul_cancel₀ _ hden]; ring
  cases cap <;> simp only [supportValue, signed_true, signed_false, chordY] <;>
    linear_combination m * hx

private theorem IsChain.signed_chord_lt {X : Finset Point} {cap : Bool} {n : ℕ}
    {f : Fin (n + 1) → Point} (hf : IsChain X cap f) {i : Fin (n + 1)}
    (hi : i ≠ 0) (hil : i ≠ Fin.last n) :
    signed cap (chordY (f 0) (f (Fin.last n)) (f i).1) < signed cap (f i).2 := by
  have hl := hf.ordered (lt_of_le_of_ne (Fin.zero_le i) hi.symm)
  have hr := hf.ordered (lt_of_le_of_ne (Fin.le_last i) hil)
  have hab := hl.trans hr
  let t := ((f i).1 - (f 0).1) / ((f (Fin.last n)).1 - (f 0).1)
  have ht0 : 0 < t := div_pos (sub_pos.mpr hl) (sub_pos.mpr hab)
  have ht1 : t < 1 := (div_lt_one (sub_pos.mpr hab)).mpr (sub_lt_sub_right hr _)
  obtain ⟨m, hm⟩ := hf.supports i
  have hleft := mul_lt_mul_of_pos_left (hm 0 hi.symm) (sub_pos.mpr ht1)
  have hright := mul_lt_mul_of_pos_left (hm (Fin.last n) hil.symm) ht0
  have hsum : (1 - t) * supportValue cap m (f 0) +
      t * supportValue cap m (f (Fin.last n)) < supportValue cap m (f i) := by
    calc
      _ < (1 - t) * supportValue cap m (f i) + t * supportValue cap m (f i) :=
        add_lt_add hleft hright
      _ = _ := by ring
  dsimp only [t] at hsum
  rw [← supportValue_chord cap m _ _ _ hab] at hsum
  exact (sub_lt_sub_iff_right _).mp hsum

private theorem flip_signed_lt {cap : Bool} {x y : ℝ}
    (h : signed (!cap) x < signed (!cap) y) : signed cap y < signed cap x := by
  cases cap
  · simpa using neg_lt_neg h
  · exact neg_lt_neg_iff.mp h

private theorem IsChain.supports_union {X : Finset Point} {cap : Bool} {n m : ℕ}
    {f : Fin (n + 1) → Point} {g : Fin (m + 1) → Point}
    (hf : IsChain X cap f) (hg : IsChain X (!cap) g)
    (hstarts : f 0 = g 0) (hends : f (Fin.last n) = g (Fin.last m))
    (i : Fin (n + 1)) :
    ∃ s : ℝ, ∀ z ∈ vertices f ∪ vertices g, z ≠ f i →
      supportValue cap s z < supportValue cap s (f i) := by
  classical
  obtain ⟨s, hs⟩ := hf.supports i
  refine ⟨s, ?_⟩
  intro z hz hne
  rcases Finset.mem_union.mp hz with hzf | hzg
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzf
    exact hs j (fun h => hne (congrArg f h))
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzg
    by_cases hj0 : j = 0
    · rw [hj0, ← hstarts] at hne ⊢
      exact hs 0 (fun h => hne (congrArg f h))
    by_cases hjl : j = Fin.last m
    · rw [hjl, ← hends] at hne ⊢
      exact hs (Fin.last n) (fun h => hne (congrArg f h))
    have hlt := flip_signed_lt (hg.signed_chord_lt hj0 hjl)
    rw [← hstarts, ← hends] at hlt
    have hab : (f 0).1 < (f (Fin.last n)).1 := by
      rw [hstarts, hends]
      exact hg.ordered
        ((lt_of_le_of_ne (Fin.zero_le j) (Ne.symm hj0)).trans
          (lt_of_le_of_ne (Fin.le_last j) hjl))
    have hl : (f 0).1 ≤ (g j).1 := by
      rw [hstarts]
      exact hg.ordered.monotone (Fin.zero_le j)
    have hr : (g j).1 ≤ (f (Fin.last n)).1 := by
      rw [hends]
      exact hg.ordered.monotone (Fin.le_last j)
    let t := ((g j).1 - (f 0).1) / ((f (Fin.last n)).1 - (f 0).1)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hl) (sub_pos.mpr hab).le
    have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hr _)
    have hle (k : Fin (n + 1)) : supportValue cap s (f k) ≤ supportValue cap s (f i) := by
      by_cases hki : k = i
      · rw [hki]
      · exact (hs k hki).le
    calc
      supportValue cap s (g j) <
          supportValue cap s ((g j).1, chordY (f 0) (f (Fin.last n)) (g j).1) :=
        sub_lt_sub_right hlt _
      _ = (1 - t) * supportValue cap s (f 0) +
          t * supportValue cap s (f (Fin.last n)) := supportValue_chord _ _ _ _ _ hab
      _ ≤ (1 - t) * supportValue cap s (f i) + t * supportValue cap s (f i) :=
        add_le_add (mul_le_mul_of_nonneg_left (hle 0) (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left (hle (Fin.last n)) ht0)
      _ = supportValue cap s (f i) := by ring

/-- The cap and cup with common endpoints form a set in convex position. -/
theorem capCup_convexPosition {X : Finset Point} {n m : ℕ}
    {f : Fin (n + 1) → Point} {g : Fin (m + 1) → Point}
    (hf : IsChain X true f) (hg : IsChain X false g)
    (hstarts : f 0 = g 0) (hends : f (Fin.last n) = g (Fin.last m)) :
    ConvexPosition (vertices f ∪ vertices g) := by
  classical
  apply convexPosition_of_support
  intro z hz
  rcases Finset.mem_union.mp hz with hzf | hzg
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzf
    obtain ⟨s, hs⟩ := hf.supports_union hg hstarts hends i
    exact ⟨true, s, hs⟩
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzg
    obtain ⟨s, hs⟩ := hg.supports_union hf hstarts.symm hends.symm i
    exact ⟨false, s, by simpa only [Finset.union_comm (vertices g) (vertices f)] using hs⟩

private theorem capCup_inter_eq {X : Finset Point} {n m : ℕ}
    {f : Fin (n + 1) → Point} {g : Fin (m + 1) → Point}
    (hf : IsChain X true f) (hg : IsChain X false g)
    (hstarts : f 0 = g 0) (hends : f (Fin.last n) = g (Fin.last m)) :
    vertices f ∩ vertices g = {f 0, f (Fin.last n)} := by
  classical
  ext z
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hzf, hzg⟩
    obtain ⟨i, _, hif⟩ := Finset.mem_image.mp hzf
    obtain ⟨j, _, hjg⟩ := Finset.mem_image.mp hzg
    by_cases hi0 : i = 0
    · exact Or.inl (hif.symm.trans (congrArg f hi0))
    by_cases hil : i = Fin.last n
    · exact Or.inr (hif.symm.trans (congrArg f hil))
    by_cases hj0 : j = 0
    · exact Or.inl (hjg.symm.trans ((congrArg g hj0).trans hstarts.symm))
    by_cases hjl : j = Fin.last m
    · exact Or.inr (hjg.symm.trans ((congrArg g hjl).trans hends.symm))
    have hcap := hf.signed_chord_lt hi0 hil
    have hcup := hg.signed_chord_lt hj0 hjl
    rw [hif] at hcap
    rw [← hstarts, ← hends, hjg] at hcup
    simp only [signed_true, signed_false] at hcap hcup
    linarith
  · rintro (rfl | rfl)
    · exact ⟨Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩,
        Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hstarts.symm⟩⟩
    · exact ⟨Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, rfl⟩,
        Finset.mem_image.mpr ⟨Fin.last m, Finset.mem_univ _, hends.symm⟩⟩

/-- The number of vertices is the sum of the two edge lengths. -/
theorem capCup_closedPolygon {X : Finset Point} {n m : ℕ}
    {f : Fin (n + 1) → Point} {g : Fin (m + 1) → Point}
    (hf : IsChain X true f) (hg : IsChain X false g) (hn : 0 < n)
    (hstarts : f 0 = g 0) (hends : f (Fin.last n) = g (Fin.last m)) :
    ConvexPosition (vertices f ∪ vertices g) ∧ (vertices f ∪ vertices g).card = n + m := by
  classical
  refine ⟨capCup_convexPosition hf hg hstarts hends, ?_⟩
  have h0n : (0 : Fin (n + 1)) < Fin.last n := hn
  have hne : f 0 ≠ f (Fin.last n) := fun hh =>
    (ne_of_lt (hf.ordered h0n)) (congrArg Prod.fst hh)
  have hc := Finset.card_union_add_card_inter (s := vertices f) (t := vertices g)
  rw [hf.card_vertices, hg.card_vertices, capCup_inter_eq hf hg hstarts hends] at hc
  have hpair : ({f 0, f (Fin.last n)} : Finset Point).card = 2 := by
    simp [Finset.card_insert_of_notMem, hne]
  omega

theorem capCup_lengths_add_le_h {X : Finset Point} {n m : ℕ}
    {f : Fin (n + 1) → Point} {g : Fin (m + 1) → Point}
    (hf : IsChain X true f) (hg : IsChain X false g) (hn : 0 < n)
    (hstarts : f 0 = g 0) (hends : f (Fin.last n) = g (Fin.last m)) :
    n + m ≤ h X := by
  obtain ⟨hConvex, hCard⟩ := capCup_closedPolygon hf hg hn hstarts hends
  rw [← hCard]
  exact hConvex.card_le_h (Finset.union_subset hf.vertices_subset hg.vertices_subset)

end ESVerify

