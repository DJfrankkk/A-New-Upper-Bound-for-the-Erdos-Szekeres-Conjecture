import ESVerify.Planar

/-! Order statistics of linear projections for the planar two-line partition. -/

noncomputable section

namespace ESVerify

open Finset

variable {α : Type*}

/-- The kth largest value, expressed as a finite maximum of finite minima. -/
private def kthLargest (S : Finset α) (k : ℕ) (hk : k ≤ S.card) (f : α → ℝ) : ℝ :=
  (S.powersetCard k).sup' (Finset.powersetCard_nonempty.mpr hk)
    (fun T => if hT : T.Nonempty then T.inf' hT f else 0)

private theorem continuous_kthLargest (S : Finset α) (k : ℕ) (hk : k ≤ S.card)
    (f : ℝ → α → ℝ) (hf : ∀ p, Continuous (fun t => f t p)) :
    Continuous (fun t => kthLargest S k hk (f t)) := by
  unfold kthLargest
  apply Continuous.finset_sup'_apply
  intro T _
  by_cases hT : T.Nonempty
  · simp only [dif_pos hT]
    exact Continuous.finset_inf'_apply hT fun p _ => hf p
  · simp only [dif_neg hT]
    exact continuous_const

private theorem kthLargest_attained (S : Finset α) (k : ℕ) (hk : k ≤ S.card) (hk0 : 0 < k)
    (f : α → ℝ) :
    ∃ T ⊆ S, T.card = k ∧ ∃ p ∈ T, kthLargest S k hk f = f p ∧ ∀ q ∈ T, f p ≤ f q := by
  obtain ⟨T, hT, heq⟩ := Finset.exists_mem_eq_sup' (Finset.powersetCard_nonempty.mpr hk)
    (fun T => if hT : T.Nonempty then T.inf' hT f else 0)
  obtain ⟨hTS, hcard⟩ := Finset.mem_powersetCard.mp hT
  have hne : T.Nonempty := Finset.card_pos.mp (hcard ▸ hk0)
  simp only [dif_pos hne] at heq
  obtain ⟨p, hp, hmin⟩ := Finset.exists_mem_eq_inf' hne f
  exact ⟨T, hTS, hcard, p, hp, heq.trans hmin, fun q hq => hmin ▸ Finset.inf'_le f hq⟩

private theorem kthLargest_mem (S : Finset α) (k : ℕ) (hk : k ≤ S.card) (hk0 : 0 < k)
    (f : α → ℝ) : ∃ p ∈ S, kthLargest S k hk f = f p := by
  obtain ⟨T, hTS, _, p, hp, heq, _⟩ := kthLargest_attained S k hk hk0 f
  exact ⟨p, hTS hp, heq⟩

private theorem ge_kthLargest_card (S : Finset α) (k : ℕ) (hk : k ≤ S.card) (hk0 : 0 < k)
    (f : α → ℝ) : k ≤ (S.filter fun p => kthLargest S k hk f ≤ f p).card := by
  obtain ⟨T, hTS, hc, p, _, heq, hmin⟩ := kthLargest_attained S k hk hk0 f
  refine hc.ge.trans (Finset.card_le_card ?_)
  exact (fun q hq => Finset.mem_filter.mpr ⟨hTS hq, heq ▸ hmin q hq⟩)

private theorem gt_kthLargest_card (S : Finset α) (k : ℕ) (hk : k ≤ S.card) (hk0 : 0 < k)
    (f : α → ℝ) : (S.filter fun p => kthLargest S k hk f < f p).card < k := by
  by_contra! he
  obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq he
  have hTS : T ⊆ S := hT.trans (Finset.filter_subset _ _)
  have hne : T.Nonempty := Finset.card_pos.mp (hc ▸ hk0)
  have hmem : T ∈ S.powersetCard k := Finset.mem_powersetCard.mpr ⟨hTS, hc⟩
  have hle : T.inf' hne f ≤ kthLargest S k hk f := by
    unfold kthLargest
    simpa only [dif_pos hne] using
      (Finset.le_sup' (fun T : Finset α => if hT : T.Nonempty then T.inf' hT f else 0) hmem)
  obtain ⟨p, hp, hpmin⟩ := Finset.exists_mem_eq_inf' hne f
  exact (not_lt_of_ge (hpmin ▸ hle)) (Finset.mem_filter.mp (hT hp)).2

private theorem paired_filter_cards {S : Finset α} {p q : α → Prop}
    [DecidablePred p] [DecidablePred q]
    (h : ∀ x ∈ S, p x ↔ ¬ q x) :
    (S.filter p).card + (S.filter q).card = S.card := by
  have hp : S.filter p = S.filter (fun x => ¬ q x) := Finset.filter_congr h
  rw [hp, add_comm]
  exact Finset.card_filter_add_card_filter_not (s := S) _

private theorem disjoint_filter_cards_le {S : Finset α} {p q : α → Prop}
    [DecidablePred p] [DecidablePred q]
    (h : ∀ x ∈ S, p x → ¬ q x) :
    (S.filter p).card + (S.filter q).card ≤ S.card := by
  have hsub : S.filter p ⊆ S.filter (fun x => ¬ q x) := by
    intro x hx
    obtain ⟨hxS, hpx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxS, h x hxS hpx⟩
  have hc := Finset.card_le_card hsub
  have hn := Finset.card_filter_add_card_filter_not (s := S) q
  omega

private structure Median (S : Finset α) (b : ℕ) : Prop where
  pos : 0 < b
  size : S.card = 2 * b

private def Median.lower {S : Finset α} {b : ℕ} (M : Median S b) (f : α → ℝ) : ℝ :=
  kthLargest S (b + 1) (by have := M.size; have := M.pos; omega) f

private def Median.upper {S : Finset α} {b : ℕ} (M : Median S b) (f : α → ℝ) : ℝ :=
  kthLargest S b (by have := M.size; omega) f

private theorem Median.lower_le_upper {S : Finset α} {b : ℕ} (M : Median S b)
    (f : α → ℝ) : M.lower f ≤ M.upper f := by
  by_contra! ht
  have hsub : (S.filter fun p => M.lower f ≤ f p) ⊆ (S.filter fun p => M.upper f < f p) := by
    intro p hp
    obtain ⟨hp, hf⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp, ht.trans_le hf⟩
  have hc := Finset.card_le_card hsub
  have hl : b + 1 ≤ (S.filter fun p => M.lower f ≤ f p).card :=
    ge_kthLargest_card S _ _ (Nat.succ_pos _) f
  have hu : (S.filter fun p => M.upper f < f p).card < b :=
    gt_kthLargest_card S _ _ M.pos f
  omega

private def Median.middle {S : Finset α} {b : ℕ} (M : Median S b) (f : α → ℝ) : ℝ :=
  (M.lower f + M.upper f) / 2

private theorem Median.continuous_middle {S : Finset α} {b : ℕ} (M : Median S b)
    (f : ℝ → α → ℝ) (hf : ∀ p, Continuous (fun t => f t p)) :
    Continuous (fun t => M.middle (f t)) :=
  ((continuous_kthLargest S _ _ f hf).add (continuous_kthLargest S _ _ f hf)).div_const 2

private theorem Median.least_card_ge {S : Finset α} {b : ℕ} (M : Median S b) (f : α → ℝ) :
    b + 1 ≤ (S.filter fun p => M.lower f ≤ f p).card :=
  ge_kthLargest_card S _ _ (Nat.succ_pos _) f

private theorem Median.least_card_le {S : Finset α} {b : ℕ} (M : Median S b) (f : α → ℝ) :
    b + 1 ≤ (S.filter fun p => f p ≤ M.upper f).card := by
  have ha : (S.filter fun p => M.upper f < f p).card < b :=
    gt_kthLargest_card S _ _ M.pos f
  have he := paired_filter_cards (S := S) (p := fun p => f p ≤ M.upper f)
    (q := fun p => M.upper f < f p) (fun _ _ => not_lt.symm)
  have hsize := M.size
  omega

private theorem Median.card_gt_le {S : Finset α} {b : ℕ} (M : Median S b)
    {f : α → ℝ} {z : ℝ} (hz : M.lower f ≤ z) :
    (S.filter fun p => z < f p).card ≤ b := by
  have hsub : (S.filter fun p => z < f p) ⊆ (S.filter fun p => M.lower f < f p) := by
    intro p hp
    obtain ⟨hp, hfp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp, hz.trans_lt hfp⟩
  have h := Finset.card_le_card hsub
  have ha : (S.filter fun p => M.lower f < f p).card < b + 1 :=
    gt_kthLargest_card S _ _ (Nat.succ_pos _) f
  omega

private theorem Median.card_lt_le {S : Finset α} {b : ℕ} (M : Median S b)
    {f : α → ℝ} {z : ℝ} (hz : z ≤ M.upper f) :
    (S.filter fun p => f p < z).card ≤ b := by
  have ha : b ≤ (S.filter fun p => M.upper f ≤ f p).card :=
    ge_kthLargest_card S _ _ M.pos f
  have hd := disjoint_filter_cards_le (S := S) (p := fun p => f p < z)
    (q := fun p => M.upper f ≤ f p) (fun p _ hp => not_le.mpr (hp.trans_le hz))
  have hsize := M.size
  omega

private theorem Median.count_sides {S : Finset α} {b : ℕ} (M : Median S b)
    {f : α → ℝ} {z : ℝ} (hl : M.lower f ≤ z) (hu : z ≤ M.upper f)
    (hn : ∀ p ∈ S, f p ≠ z) :
    (S.filter fun p => f p < z).card = b ∧ (S.filter fun p => z < f p).card = b := by
  have ha := M.card_lt_le hu
  have hb := M.card_gt_le hl
  have he := paired_filter_cards (S := S) (p := fun p => f p < z)
    (q := fun p => z < f p) (fun p hp => by
      rw [not_lt]
      exact le_iff_lt_or_eq.trans (by simp [hn p hp]) |>.symm)
  have hsize := M.size
  omega

private theorem Median.no_ties_between {S : Finset α} {b : ℕ} (M : Median S b)
    {f : α → ℝ} {z : ℝ} (hl : M.lower f < z) (hu : z < M.upper f) :
    ∀ p ∈ S, f p ≠ z := by
  intro p hp heq
  have hsub : (S.filter fun q => M.upper f ≤ f q) ⊆ (S.filter fun q => M.lower f < f q) := by
    intro q hq
    obtain ⟨hq, hf⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq, hl.trans (hu.trans_le hf)⟩
  have hnot : p ∉ S.filter fun q => M.upper f ≤ f q := by simp [hp, heq, not_le.mpr hu]
  have hps : p ∈ S.filter fun q => M.lower f < f q := Finset.mem_filter.mpr ⟨hp, heq ▸ hl⟩
  classical
  have hsub' := Finset.insert_subset hps hsub
  have hc := Finset.card_le_card hsub'
  rw [Finset.card_insert_of_notMem hnot] at hc
  have ha : b ≤ (S.filter fun p => M.upper f ≤ f p).card :=
    ge_kthLargest_card S _ _ M.pos f
  have hb : (S.filter fun p => M.lower f < f p).card < b + 1 :=
    gt_kthLargest_card S _ _ (Nat.succ_pos _) f
  omega

private theorem Median.ties_card_ge {S : Finset α} {b : ℕ} (M : Median S b)
    {f : α → ℝ} {z : ℝ} (hl : M.lower f = z) (hu : M.upper f = z) :
    2 ≤ (S.filter fun p => f p = z).card := by
  classical
  let G := S.filter fun p => z ≤ f p
  let L := S.filter fun p => f p ≤ z
  have hg : b + 1 ≤ G.card := by simpa [G, hl] using M.least_card_ge f
  have hle : b + 1 ≤ L.card := by simpa [L, hu] using M.least_card_le f
  have hsub : G ∪ L ⊆ S := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hboth : G ∩ L = S.filter (fun p => f p = z) := by
    ext p
    simp only [G, L, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, hgp⟩, _, hlp⟩
      exact ⟨hp, le_antisymm hlp hgp⟩
    · rintro ⟨hp, rfl⟩
      exact ⟨⟨hp, le_rfl⟩, hp, le_rfl⟩
  have hc := Finset.card_union_add_card_inter G L
  have hcard := Finset.card_le_card hsub
  rw [hboth] at hc
  have hsize := M.size
  omega

private theorem Median.ties_card_ge_of_tie {S : Finset α} {b : ℕ} (M : Median S b)
    {f : α → ℝ} {p : α} (hp : p ∈ S) (he : f p = M.middle f) :
    2 ≤ (S.filter fun p => f p = M.middle f).card := by
  have hh := M.lower_le_upper f
  by_cases hl : M.lower f < M.upper f
  · have h₁ : M.lower f < M.middle f := by unfold Median.middle; linarith
    have h₂ : M.middle f < M.upper f := by unfold Median.middle; linarith
    exact False.elim (M.no_ties_between h₁ h₂ p hp he)
  · have h₁ : M.lower f = M.middle f := by unfold Median.middle; linarith
    have h₂ : M.upper f = M.middle f := by unfold Median.middle; linarith
    exact M.ties_card_ge h₁ h₂

private theorem Median.count_middle {S : Finset α} {b : ℕ} (M : Median S b)
    {f : α → ℝ} (hna : ∀ p ∈ S, f p ≠ M.middle f) :
    (S.filter fun p => f p < M.middle f).card = b ∧
    (S.filter fun p => M.middle f < f p).card = b := by
  have hm := M.lower_le_upper f
  refine M.count_sides ?_ ?_ hna <;> unfold Median.middle <;> linarith

private theorem Median.middle_untied_of_injective {S : Finset α} {b : ℕ} (M : Median S b)
    {f : α → ℝ} (hf : Set.InjOn f S) :
    ∀ p ∈ S, f p ≠ M.middle f := by
  intro p hp heq
  have hh := M.ties_card_ge_of_tie hp heq
  have hsmall : (S.filter fun p => f p = M.middle f).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxS, hxF⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyS, hyF⟩ := Finset.mem_filter.mp hy
    exact hf hxS hyS (hxF.trans hyF.symm)
  omega

private theorem Median.middle_lt_middle {S T : Finset α} {b c : ℕ}
    (M : Median S b) (N : Median T c) {f : α → ℝ}
    (hf : ∀ p ∈ S, ∀ q ∈ T, f p < f q) : M.middle f < N.middle f := by
  obtain ⟨p, hp, he₁⟩ : ∃ p ∈ S, M.upper f = f p := kthLargest_mem S _ _ M.pos f
  obtain ⟨q, hq, he₂⟩ : ∃ q ∈ T, N.lower f = f q := kthLargest_mem T _ _ (Nat.succ_pos _) f
  have hi := hf p hp q hq
  have h₁ := M.lower_le_upper f
  have h₂ := N.lower_le_upper f
  unfold Median.middle
  linarith

/-- If the line meets just two points of a half, rotating it to pass between them
preserves the balance in that half. The other half has unchanged signs. -/
private theorem Median.count_perturbed {S : Finset α} {b : ℕ} (M : Median S b)
    {f g : α → ℝ} {z w : ℝ} {r s : α} (hrs : r ≠ s)
    (hS : r ∈ S ↔ s ∈ S) (hr : f r = z) (hs : f s = z)
    (hgr : g r < w) (hgs : w < g s)
    (hties : ∀ p ∈ S, f p = z → p = r ∨ p = s)
    (hsgn : ∀ p ∈ S, (f p < z → g p < w) ∧ (z < f p → w < g p))
    (hmid : M.middle f = z) :
    (S.filter fun p => g p < w).card = b ∧ (S.filter fun p => w < g p).card = b := by
  classical
  by_cases hm : r ∈ S
  · have hms := hS.mp hm
    let L := S.filter fun p => f p < z
    let R := S.filter fun p => z < f p
    have hL : (S.filter fun p => g p < w) = insert r L := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert, L]
      constructor
      · rintro ⟨hp, hgp⟩
        rcases lt_trichotomy (f p) z with hf | hf | hf
        · exact Or.inr ⟨hp, hf⟩
        · rcases hties p hp hf with h | h
          · exact Or.inl h
          · rw [h] at hgp
            exact False.elim ((not_lt_of_gt hgs) hgp)
        · exact False.elim ((not_lt_of_gt ((hsgn p hp).2 hf)) hgp)
      · rintro (rfl | ⟨hp, hf⟩)
        · exact ⟨hm, hgr⟩
        · exact ⟨hp, (hsgn p hp).1 hf⟩
    have hR : (S.filter fun p => w < g p) = insert s R := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert, R]
      constructor
      · rintro ⟨hp, hgp⟩
        rcases lt_trichotomy (f p) z with hf | hf | hf
        · exact False.elim ((not_lt_of_gt ((hsgn p hp).1 hf)) hgp)
        · rcases hties p hp hf with h | h
          · rw [h] at hgp
            exact False.elim ((not_lt_of_gt hgr) hgp)
          · exact Or.inl h
        · exact Or.inr ⟨hp, hf⟩
      · rintro (rfl | ⟨hp, hf⟩)
        · exact ⟨hms, hgs⟩
        · exact ⟨hp, (hsgn p hp).2 hf⟩
    have hd : (L ∪ R) = S.filter (fun p => f p ≠ z) := by
      ext p
      simp only [L, R, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hp, h⟩ | ⟨hp, h⟩)
        · exact ⟨hp, ne_of_lt h⟩
        · exact ⟨hp, ne_of_gt h⟩
      · rintro ⟨hp, hne⟩
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr ⟨hp, h⟩
    have he : S.filter (fun p => f p = z) = {r, s} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => hties p h.1 h.2
      · rintro (rfl | rfl)
        · exact ⟨hm, hr⟩
        · exact ⟨hms, hs⟩
    have hi : (L ∩ R).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have hf := Finset.mem_filter.mp (Finset.mem_inter.mp hp).1
      have hg := Finset.mem_filter.mp (Finset.mem_inter.mp hp).2
      exact (not_lt_of_gt hf.2) hg.2
    have hh := Finset.card_union_add_card_inter L R
    rw [hi, add_zero, hd] at hh
    have hc := Finset.card_filter_add_card_filter_not (s := S) (fun p => f p = z)
    rw [he, Finset.card_pair hrs, hh] at hc
    have h₁ : r ∉ L := by simp [L, hr]
    have h₂ : s ∉ R := by simp [R, hs]
    rw [hL, hR, Finset.card_insert_of_notMem h₁, Finset.card_insert_of_notMem h₂]
    have hsize := M.size
    have hLowUp := M.lower_le_upper f
    have hLowUpEq : M.lower f = M.upper f := by
      apply le_antisymm hLowUp
      by_contra! hlt
      have h₁ : M.lower f < z := by unfold Median.middle at hmid; linarith
      have h₂ : z < M.upper f := by unfold Median.middle at hmid; linarith
      exact M.no_ties_between h₁ h₂ r hm hr
    have hzl : M.lower f = z := by unfold Median.middle at hmid; linarith
    have hzu : M.upper f = z := by unfold Median.middle at hmid; linarith
    have hAbove := M.least_card_ge f
    have hBelow := M.least_card_le f
    rw [hzl] at hAbove
    rw [hzu] at hBelow
    have hAc : (S.filter fun p => z ≤ f p).card + L.card = S.card :=
      paired_filter_cards (fun _ _ => not_lt.symm)
    have hBc : (S.filter fun p => f p ≤ z).card + R.card = S.card :=
      paired_filter_cards (fun _ _ => not_lt.symm)
    omega
  · have hms : s ∉ S := fun h => hm (hS.mpr h)
    have hf : ∀ p ∈ S, f p ≠ z := fun p hp ht =>
      (hties p hp ht).elim (fun h => hm (h ▸ hp)) (fun h => hms (h ▸ hp))
    have hf' : ∀ p ∈ S, f p ≠ M.middle f := by simpa [hmid] using hf
    obtain ⟨hL, hR⟩ := M.count_middle hf'
    rw [hmid] at hL hR
    have eL : (S.filter fun p => g p < w) = S.filter (fun p => f p < z) := by
      apply Finset.filter_congr
      intro p hp
      rcases lt_or_gt_of_ne (hf p hp) with h | h
      · simp [h, (hsgn p hp).1 h]
      · simp [not_lt_of_gt h, not_lt_of_gt ((hsgn p hp).2 h)]
    have eR : (S.filter fun p => w < g p) = S.filter (fun p => z < f p) := by
      apply Finset.filter_congr
      intro p hp
      rcases lt_or_gt_of_ne (hf p hp) with h | h
      · simp [not_lt_of_gt h, not_lt_of_gt ((hsgn p hp).1 h)]
      · simp [h, (hsgn p hp).2 h]
    simpa [eL, eR] using And.intro hL hR

open Filter Topology

private def projection (t : ℝ) (p : Point) : ℝ := t * p.1 + p.2

private theorem continuous_projection (p : Point) : Continuous (fun t => projection t p) := by
  unfold projection
  fun_prop

private theorem third_projection_eq {E : Finset Point} (hg : GeneralPosition E)
    {r s p : Point} (hr : r ∈ E) (hs : s ∈ E) (hp : p ∈ E) (hrs : r ≠ s)
    {t z : ℝ} (h₁ : projection t r = z) (h₂ : projection t s = z) (h₃ : projection t p = z) :
    p = r ∨ p = s := by
  by_contra! hn
  apply hg r hr s hs p hp hrs (Ne.symm hn.1) (Ne.symm hn.2)
  have he₁ : s.2 - r.2 = -t * (s.1 - r.1) := by
    unfold projection at h₁ h₂
    linarith
  have he₂ : p.2 - r.2 = -t * (p.1 - r.1) := by
    unfold projection at h₁ h₃
    linarith
  unfold orientation
  rw [he₁, he₂]
  ring

private theorem projection_eq_at_some_slope {L R : Finset Point} {b : ℕ}
    (ML : Median L b) (MR : Median R b)
    (hord : ∀ p ∈ L, ∀ q ∈ R, p.1 < q.1) :
    ∃ t : ℝ, ML.middle (projection t) = MR.middle (projection t) := by
  classical
  let cuts : Finset ℝ := (L.product R).image
    (fun pq => (pq.1.2 - pq.2.2) / (pq.2.1 - pq.1.1))
  obtain ⟨lo, hlo⟩ := cuts.finite_toSet.bddBelow
  obtain ⟨hi, hhi⟩ := cuts.finite_toSet.bddAbove
  let a := min lo hi - 1
  let c := max lo hi + 1
  have hac : a ≤ c := by
    have h₁ := min_le_left lo hi
    have h₂ := le_max_left lo hi
    dsimp [a, c]
    linarith
  have hcross {p q : Point} (hp : p ∈ L) (hq : q ∈ R) :
      (p.2 - q.2) / (q.1 - p.1) ∈ cuts := by
    exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
  have ha : ∀ q ∈ R, ∀ p ∈ L, projection a q < projection a p := by
    intro q hq p hp
    have h₁ : a < lo := by dsimp [a]; linarith [min_le_left lo hi]
    have h₂ := hlo (hcross hp hq)
    have h₃ := (lt_div_iff₀ (sub_pos.mpr (hord p hp q hq))).mp (h₁.trans_le h₂)
    unfold projection
    linarith
  have hc : ∀ p ∈ L, ∀ q ∈ R, projection c p < projection c q := by
    intro p hp q hq
    have h₁ : hi < c := by dsimp [c]; linarith [le_max_right lo hi]
    have h₂ := hhi (hcross hp hq)
    have h₃ := (div_lt_iff₀ (sub_pos.mpr (hord p hp q hq))).mp (h₂.trans_lt h₁)
    unfold projection
    linarith
  let g (t : ℝ) := MR.middle (projection t) - ML.middle (projection t)
  have hg : Continuous g := (MR.continuous_middle projection continuous_projection).sub
    (ML.continuous_middle projection continuous_projection)
  have h₁ : g a ≤ 0 := sub_nonpos.mpr (MR.middle_lt_middle ML ha).le
  have h₂ : 0 ≤ g c := sub_nonneg.mpr (ML.middle_lt_middle MR hc).le
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hac hg.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (g a) (g c) from ⟨h₁, h₂⟩)
  exact ⟨t, (sub_eq_zero.mp ht).symm⟩

private theorem exists_bisecting_projection {E L R : Finset Point} {b : ℕ}
    (ML : Median L b) (MR : Median R b) (hLE : L ⊆ E) (hRE : R ⊆ E)
    (hcover : ∀ p ∈ E, p ∈ L ∨ p ∈ R)
    (hord : ∀ p ∈ L, ∀ q ∈ R, p.1 < q.1)
    (hg : GeneralPosition E) (hx : DistinctAbscissae E) :
    ∃ t z : ℝ,
      (L.filter fun p => projection t p < z).card = b ∧
      (L.filter fun p => z < projection t p).card = b ∧
      (R.filter fun p => projection t p < z).card = b ∧
      (R.filter fun p => z < projection t p).card = b := by
  classical
  obtain ⟨t, ht⟩ := projection_eq_at_some_slope ML MR hord
  let z := ML.middle (projection t)
  have hLz : ML.middle (projection t) = z := rfl
  have hRz : MR.middle (projection t) = z := ht.symm
  by_cases hnone : ∀ p ∈ E, projection t p ≠ z
  · obtain ⟨hLa, hLb⟩ := ML.count_middle (f := projection t) (fun p hp => hnone p (hLE hp))
    obtain ⟨hRa, hRb⟩ := MR.count_middle (f := projection t) (fun p hp => by
      rw [hRz]; exact hnone p (hRE hp))
    rw [hRz] at hRa hRb
    exact ⟨t, z, hLa, hLb, hRa, hRb⟩
  push Not at hnone
  obtain ⟨p, hp, hpz⟩ := hnone
  let S := if p ∈ L then L else R
  have hpS : p ∈ S := by
    dsimp [S]
    split_ifs with h
    · exact h
    · exact (hcover p hp).resolve_left h
  have hsub : S ⊆ E := by
    dsimp [S]
    split_ifs
    · exact hLE
    · exact hRE
  have M : Median S b := by
    dsimp [S]
    split_ifs
    · exact ML
    · exact MR
  have hMz : M.middle (projection t) = z := by
    by_cases hpL : p ∈ L
    · have he : S = L := if_pos hpL
      revert M
      rw [he]
      exact fun _ => hLz
    · have he : S = R := if_neg hpL
      revert M
      rw [he]
      exact fun _ => hRz
  have hcard : 1 < (S.filter fun p => projection t p = z).card := by
    have hge := M.ties_card_ge_of_tie hpS (hpz.trans hMz.symm)
    rw [hMz] at hge
    omega
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨haS, haT⟩ := Finset.mem_filter.mp ha
  obtain ⟨hcS, hcT⟩ := Finset.mem_filter.mp hc
  have hne : a.1 ≠ c.1 := fun h => hac (hx (hsub haS) (hsub hcS) h)
  obtain ⟨r, s, hrS, hsS, hr, hs, hrs⟩ :
      ∃ r s, r ∈ S ∧ s ∈ S ∧ projection t r = z ∧ projection t s = z ∧ r.1 < s.1 := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, c, haS, hcS, haT, hcT, h⟩
    · exact ⟨c, a, hcS, haS, hcT, haT, h⟩
  have hrs' : r ≠ s := fun h => (ne_of_lt hrs) (congrArg Prod.fst h)
  have hties : ∀ q ∈ E, projection t q = z → q = r ∨ q = s := fun q hq h =>
    third_projection_eq hg (hsub hrS) (hsub hsS) hq hrs' hr hs h
  let cut (u : ℝ) := (projection u r + projection u s) / 2
  have hcut : cut t = z := by dsimp [cut]; linarith
  have hct : Continuous cut := ((continuous_projection r).add (continuous_projection s)).div_const 2
  have hsgn : ∀ᶠ u in 𝓝 t, ∀ q ∈ E,
      (projection t q < z → projection u q < cut u) ∧
      (z < projection t q → cut u < projection u q) := by
    apply (E.finite_toSet.eventually_all).mpr
    intro q _
    by_cases hl : projection t q < z
    · have he := (continuous_projection q).continuousAt.eventually_lt hct.continuousAt
        (show projection t q < cut t by rw [hcut]; exact hl)
      exact he.mono fun u hu => ⟨fun _ => hu, fun h => (lt_asymm hl h).elim⟩
    · by_cases hr : z < projection t q
      · have he := hct.continuousAt.eventually_lt (continuous_projection q).continuousAt
          (show cut t < projection t q by rw [hcut]; exact hr)
        exact he.mono fun u hu => ⟨fun h => (hl h).elim, fun _ => hu⟩
      · exact Filter.Eventually.of_forall fun u => ⟨fun h => (hl h).elim, fun h => (hr h).elim⟩
  obtain ⟨u, hut, hsu⟩ := hsgn.exists_gt
  have hless : projection u r < projection u s := by
    have hmul := mul_pos (sub_pos.mpr hut) (sub_pos.mpr hrs)
    unfold projection at hr hs ⊢
    nlinarith
  have hru : projection u r < cut u := by unfold cut; linarith
  have hsu' : cut u < projection u s := by unfold cut; linarith
  have hLR {q : Point} (hq : q ∈ L) : q ∉ R :=
    fun h => (lt_irrefl q.1) (hord q hq q h)
  have hRS : (r ∈ L ↔ s ∈ L) ∧ (r ∈ R ↔ s ∈ R) := by
    by_cases hpL : p ∈ L
    · have hrL : r ∈ L := by simpa [S, hpL] using hrS
      have hsL : s ∈ L := by simpa [S, hpL] using hsS
      exact ⟨iff_of_true hrL hsL, iff_of_false (hLR hrL) (hLR hsL)⟩
    · have hrR : r ∈ R := by simpa [S, hpL] using hrS
      have hsR : s ∈ R := by simpa [S, hpL] using hsS
      exact ⟨iff_of_false (fun h => hLR h hrR) (fun h => hLR h hsR), iff_of_true hrR hsR⟩
  obtain ⟨hLa, hLb⟩ := ML.count_perturbed hrs' hRS.1 hr hs hru hsu'
    (fun q hq => hties q (hLE hq)) (fun q hq => hsu q (hLE hq)) hLz
  obtain ⟨hRa, hRb⟩ := MR.count_perturbed hrs' hRS.2 hr hs hru hsu'
    (fun q hq => hties q (hRE hq)) (fun q hq => hsu q (hRE hq)) hRz
  exact ⟨u, cut u, hLa, hLb, hRa, hRb⟩

/-- A vertical line and one nonvertical line form a two-line equipartition
of any general-position set with (4b) points and distinct abscissae. -/
theorem equipartition_cuts {E : Finset Point} (hg : GeneralPosition E)
    (hx : DistinctAbscissae E) (b : ℕ) (hb : 0 < b) (hcard : E.card = 4 * b) :
    ∃ a t z : ℝ,
      let L := E.filter fun p => p.1 < a
      let R := E.filter fun p => a < p.1
      (L.filter fun p => t * p.1 + p.2 < z).card = b ∧
      (L.filter fun p => z < t * p.1 + p.2).card = b ∧
      (R.filter fun p => t * p.1 + p.2 < z).card = b ∧
      (R.filter fun p => z < t * p.1 + p.2).card = b := by
  have MV : Median E (2 * b) := ⟨by omega, by omega⟩
  let a := MV.middle Prod.fst
  let L := E.filter fun p => p.1 < a
  let R := E.filter fun p => a < p.1
  have hnone : ∀ p ∈ E, p.1 ≠ a := MV.middle_untied_of_injective hx
  obtain ⟨hL, hR⟩ := MV.count_middle hnone
  have ML : Median L b := ⟨hb, hL⟩
  have MR : Median R b := ⟨hb, hR⟩
  have hLE : L ⊆ E := Finset.filter_subset _ _
  have hRE : R ⊆ E := Finset.filter_subset _ _
  have hcover : ∀ p ∈ E, p ∈ L ∨ p ∈ R := by
    intro p hp
    rcases lt_or_gt_of_ne (hnone p hp) with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hp, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hp, h⟩)
  have hord : ∀ p ∈ L, ∀ q ∈ R, p.1 < q.1 := by
    intro p hp q hq
    exact ((Finset.mem_filter.mp hp).2).trans ((Finset.mem_filter.mp hq).2)
  obtain ⟨t, z, hz⟩ := exists_bisecting_projection ML MR hLE hRE hcover hord hg hx
  exact ⟨a, t, z, hz⟩

end ESVerify