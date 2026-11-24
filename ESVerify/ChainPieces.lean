import ESVerify.Planar
import ESVerify.RankAlternative

set_option autoImplicit false

namespace ESVerify

private def segment {n : ℕ} (p : Fin (n + 1) → Point) (s m : ℕ) (hm : s + m ≤ n) :
    Fin (m + 1) → Point := fun i => p ⟨s + i, by omega⟩

private theorem edgeSlope_segment {n : ℕ} (p : Fin (n + 1) → Point) (s m : ℕ)
    (hm : s + m ≤ n) (i : Fin m) :
    edgeSlope (segment p s m hm) i = edgeSlope p ⟨s + i, by omega⟩ := by
  rfl

private theorem segment_chain {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) (s m : ℕ) (hm : s + m ≤ n) :
    IsChain X cap (segment p s m hm) where
  mem i := hp.mem _
  ordered := by
    intro i j hij
    apply hp.ordered
    change s + i.val < s + j.val
    exact Nat.add_lt_add_left hij s
  slopes := by
    intro i j hij
    change signed cap (edgeSlope (segment p s m hm) j) < signed cap (edgeSlope (segment p s m hm) i)
    rw [edgeSlope_segment, edgeSlope_segment]
    apply hp.slopes
    change s + i.val < s + j.val
    exact Nat.add_lt_add_left hij s

private def glue {m n : ℕ} (p : Fin (m + 1) → Point) (q : Fin (n + 1) → Point)
    (i : Fin (m + n + 1)) : Point :=
  if h : i.val ≤ m then p ⟨i.val, by omega⟩ else q ⟨i.val - m, by omega⟩

private theorem glue_left {m n : ℕ} (p : Fin (m + 1) → Point) (q : Fin (n + 1) → Point)
    (i : Fin (m + n + 1)) (hi : i.val ≤ m) :
    glue p q i = p ⟨i.val, by omega⟩ := by simp [glue, hi]

private theorem glue_right {m n : ℕ} (p : Fin (m + 1) → Point) (q : Fin (n + 1) → Point)
    (hjoin : p (Fin.last m) = q 0) (i : Fin (m + n + 1)) (hi : m ≤ i.val) :
    glue p q i = q ⟨i.val - m, by omega⟩ := by
  by_cases hi' : i.val ≤ m
  · have hi'' : i.val = m := by omega
    rw [glue_left _ _ _ hi']
    have hp : (⟨i.val, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext hi''
    have hq : (⟨i.val - m, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext (by simp [hi''])
    rwa [hp, hq]
  · simp [glue, hi']

private theorem edgeSlope_glue_left {m n : ℕ} (p : Fin (m + 1) → Point)
    (q : Fin (n + 1) → Point) (i : Fin (m + n)) (hi : i.val < m) :
    edgeSlope (glue p q) i = edgeSlope p ⟨i.val, hi⟩ := by
  unfold edgeSlope
  rw [glue_left _ _ _ (by simpa using hi.le), glue_left _ _ _ (by simpa using hi)]
  rfl

private theorem edgeSlope_glue_right {m n : ℕ} (p : Fin (m + 1) → Point)
    (q : Fin (n + 1) → Point) (hjoin : p (Fin.last m) = q 0)
    (i : Fin (m + n)) (hi : m ≤ i.val) :
    edgeSlope (glue p q) i = edgeSlope q ⟨i.val - m, by omega⟩ := by
  unfold edgeSlope
  rw [glue_right _ _ hjoin _ (by simpa using hi), glue_right _ _ hjoin _ (by simp; omega)]
  congr 2
  apply Fin.ext
  simp
  omega

private theorem glue_chain {X : Finset Point} {cap : Bool} {m n : ℕ}
    {p : Fin (m + 1) → Point} {q : Fin (n + 1) → Point}
    (hp : IsChain X cap p) (hq : IsChain X cap q) (hjoin : p (Fin.last m) = q 0)
    (hcompat : ∀ i : Fin m, ∀ j : Fin n,
      signed cap (edgeSlope q j) < signed cap (edgeSlope p i)) :
    IsChain X cap (glue p q) := by
  constructor
  · intro i
    by_cases hi : i.val ≤ m
    · rw [glue_left _ _ _ hi]
      exact hp.mem _
    · rw [glue_right _ _ hjoin _ (by omega)]
      exact hq.mem _
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    by_cases hi : i.val < m
    · rw [glue_left _ _ _ (by simpa using hi.le), glue_left _ _ _ (by simpa using hi)]
      apply hp.ordered
      change i.val < i.val + 1
      omega
    · rw [glue_right _ _ hjoin _ (by simp; omega), glue_right _ _ hjoin _ (by simp; omega)]
      apply hq.ordered
      change i.val - m < i.val + 1 - m
      omega
  · intro i j hij
    have hij' : i.val < j.val := hij
    change signed cap (edgeSlope (glue p q) j) < signed cap (edgeSlope (glue p q) i)
    by_cases hi : i.val < m
    · by_cases hj : j.val < m
      · rw [edgeSlope_glue_left _ _ _ hi, edgeSlope_glue_left _ _ _ hj]
        exact hp.slopes hij'
      · rw [edgeSlope_glue_left _ _ _ hi, edgeSlope_glue_right _ _ hjoin _ (by omega)]
        exact hcompat _ _
    · rw [edgeSlope_glue_right _ _ hjoin _ (by omega), edgeSlope_glue_right _ _ hjoin _ (by omega)]
      apply hq.slopes
      change i.val - m < j.val - m
      omega

/-- The segment between two points in one group lies strictly on the first side
of the joining slope at either endpoint. For caps this denotes a positive edge,
and for cups a negative edge. -/
def FirstSide (cap : Bool) (G : Finset Point) (p q : Point) : Prop :=
  ∀ w ∈ G, signed cap (slope p w) < signed cap (slope p q) ∧
    signed cap (slope q w) < signed cap (slope p q)

private theorem lastSide_lt {cap : Bool} {G : Finset Point} {p q w : Point}
    (h : FirstSide (!cap) G p q) (hw : w ∈ G) :
    signed cap (slope p q) < signed cap (slope p w) ∧
      signed cap (slope p q) < signed cap (slope q w) := by
  have hh := h w hw
  cases cap <;> simpa [neg_lt_neg_iff] using hh

theorem slope_comm (p q : Point) : slope p q = slope q p := by
  calc
    slope p q = (-(q.2 - p.2)) / (-(q.1 - p.1)) := (neg_div_neg_eq _ _).symm
    _ = slope q p := by unfold slope; congr 1 <;> ring

private theorem initial_edges {n : ℕ} (P : Fin n → Prop)
    (hprev : ∀ i : ℕ, ∀ hi : i + 1 < n,
      P ⟨i + 1, hi⟩ → P ⟨i, by omega⟩) :
    ∃ k ≤ n, ∀ i : Fin n, P i ↔ i.val < k := by
  classical
  let P' (i : ℕ) : Prop := ∃ hi : i < n, P ⟨i, hi⟩
  have hn : ¬ P' n := fun ⟨hin, _⟩ => (lt_irrefl _ hin)
  have hex : ∃ i, ¬ P' i := ⟨n, hn⟩
  let k := Nat.find hex
  have hk : k ≤ n := Nat.find_min' hex hn
  have hkbad : ¬ P' k := Nat.find_spec hex
  have hbad : ∀ t : ℕ, ¬ P' (k + t) := by
    intro t
    induction t with
    | zero => simpa using hkbad
    | succ t ih =>
      rintro ⟨hi, h'⟩
      exact ih ⟨by omega, hprev (k + t) hi h'⟩
  refine ⟨k, hk, fun i => ⟨?_, ?_⟩⟩
  · intro hi
    by_contra hnlt
    have he : k + (i.val - k) = i.val := by omega
    apply hbad (i.val - k)
    rw [he]
    exact ⟨i.isLt, hi⟩
  · intro hi
    have hh : P' i.val := by
      by_contra h
      exact (Nat.not_le_of_lt hi) (Nat.find_min' hex h)
    exact hh.choose_spec

private theorem signed_eligible_of_all {cap : Bool} {n : ℕ} {p : Fin (n + 1) → Point}
    {t : ℝ} (hall : ∀ i : Fin n, signed cap t ≤ signed cap (edgeSlope p i)) :
    LastEdgeEligible cap p t := by
  cases n with
  | zero => trivial
  | succ n => exact hall (Fin.last n)

private theorem signed_all_of_eligible {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p)
    {t : ℝ} (ht : LastEdgeEligible cap p t) :
    ∀ i : Fin n, signed cap t ≤ signed cap (edgeSlope p i) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n => exact fun i => ht.trans (hp.slopes.antitone (Fin.le_last i))

private def IsPiece (G K : Finset Point) (cap front : Bool) (u : Point)
    {n : ℕ} (p : Fin (n + 1) → Point) : Prop :=
  IsChain G cap p ∧ (if front then p 0 = u else p (Fin.last n) = u) ∧
    ∀ i : Fin n, FirstSide (if front then cap else !cap) K (p i.castSucc) (p i.succ)

private noncomputable def pieceLength (G K : Finset Point) (cap front : Bool) (u : Point) : ℕ :=
  sSup {n | n = 0 ∨ ∃ p : Fin (n + 1) → Point, IsPiece G K cap front u p}

private theorem pieceLength_bddAbove (G K : Finset Point) (cap front : Bool) (u : Point) :
    BddAbove {n | n = 0 ∨ ∃ p : Fin (n + 1) → Point, IsPiece G K cap front u p} := by
  refine ⟨maxLength G cap, ?_⟩
  rintro n (rfl | ⟨p, hp⟩)
  · exact Nat.zero_le _
  · exact hp.1.le_maxLength

private theorem le_pieceLength {G K : Finset Point} {cap front : Bool} {u : Point}
    {n : ℕ} {p : Fin (n + 1) → Point} (hp : IsPiece G K cap front u p) :
    n ≤ pieceLength G K cap front u :=
  le_csSup (pieceLength_bddAbove G K cap front u) (Or.inr ⟨p, hp⟩)

private theorem pieceLength_attained {G K : Finset Point} {cap front : Bool} {u : Point}
    (hu : u ∈ G) : ∃ p : Fin (pieceLength G K cap front u + 1) → Point,
      IsPiece G K cap front u p := by
  have hmem := Nat.sSup_mem (Set.nonempty_of_mem (Or.inl rfl : (0 : ℕ) = 0 ∨
    ∃ p : Fin (0 + 1) → Point, IsPiece G K cap front u p)) (pieceLength_bddAbove G K cap front u)
  change pieceLength G K cap front u = 0 ∨ _ at hmem
  rcases hmem with hzero | hpiece
  · rw [hzero]
    exact ⟨fun _ => u, singleton_chain hu, by cases front <;> rfl, Fin.elim0⟩
  · exact hpiece

private theorem front_eligible {cap : Bool} {G : Finset Point} {m : ℕ}
    {p : Fin (m + 1) → Point} {w : Point}
    (hs : ∀ i : Fin m, FirstSide cap G (p i.castSucc) (p i.succ)) (hw : w ∈ G) :
    LastEdgeEligible cap p (slope (p (Fin.last m)) w) := by
  cases m with
  | zero => trivial
  | succ m =>
    have hh := (hs (Fin.last m) w hw).2
    simpa [LastEdgeEligible, edgeSlope, Fin.succ_last] using hh.le

private theorem back_all_lt {X G : Finset Point} {cap : Bool} {m : ℕ}
    {p : Fin (m + 1) → Point} {w : Point}
    (hp : IsChain X cap p) (hs : ∀ i : Fin m, FirstSide (!cap) G (p i.castSucc) (p i.succ))
    (hw : w ∈ G) : ∀ i : Fin m, signed cap (edgeSlope p i) < signed cap (slope (p 0) w) := by
  cases m with
  | zero => intro i; exact Fin.elim0 i
  | succ m =>
    intro i
    apply lt_of_le_of_lt (hp.slopes.antitone (Fin.zero_le i))
    exact (lastSide_lt (hs 0) hw).1

private theorem cross_front_all_lt {X G : Finset Point} {cap : Bool} {m : ℕ}
    {p : Fin (m + 1) → Point} {w : Point}
    (hp : IsChain X cap p) (hs : ∀ i : Fin m, FirstSide cap G (p i.castSucc) (p i.succ))
    (hw : w ∈ G) :
    ∀ i : Fin m, signed cap (slope (p (Fin.last m)) w) < signed cap (edgeSlope p i) := by
  cases m with
  | zero => intro i; exact Fin.elim0 i
  | succ m =>
    intro i
    apply lt_of_lt_of_le _ (hp.slopes.antitone (Fin.le_last i))
    simpa [edgeSlope, Fin.succ_last] using (hs (Fin.last m) w hw).2

/-- Lemma 4.1 in a form recording the retained endpoints of the two pieces.
Taking `cap = false` exchanges “positive” and “negative”. -/
private theorem split_planar {X G K : Finset Point} {cap : Bool} {r : ℕ}
    (hGX : G ⊆ X) (hneK : K.Nonempty)
    (hrank : ∀ u ∈ G, ∀ w ∈ K, endingRank X cap u (slope u w) = r)
    (hside : ∀ p ∈ G, ∀ q ∈ G, p.1 < q.1 → FirstSide cap K p q ∨ FirstSide (!cap) K p q) :
    SectionFourSplit G (fun H => maxLength H cap) (maxLength X cap) r
      (pieceLength G K cap true) (pieceLength G K cap false) := by
  intro H hneH hHG
  obtain ⟨w, hw⟩ := hneK
  obtain ⟨p, hp⟩ := maxLength_attained hneH cap
  let n := maxLength H cap
  let P (i : Fin n) := FirstSide cap K (p i.castSucc) (p i.succ)
  have hs (i : Fin n) : P i ∨ FirstSide (!cap) K (p i.castSucc) (p i.succ) :=
    hside _ (hHG (hp.mem _)) _ (hHG (hp.mem _)) (hp.ordered (Fin.castSucc_lt_succ (i := i)))
  obtain ⟨a, han, ha⟩ := initial_edges P (by
    intro i hi hpos
    let j : Fin n := ⟨i, by omega⟩
    let k : Fin n := ⟨i + 1, hi⟩
    rcases hs j with h | h
    · exact h
    · have hj := (lastSide_lt h hw).2
      have hk := (hpos w hw).1
      have hlt := hp.slopes (show j < k from Nat.lt_succ_self i)
      change signed cap (edgeSlope p j) < signed cap (slope (p j.succ) w) at hj
      change signed cap (slope (p k.castSucc) w) < signed cap (edgeSlope p k) at hk
      have heq : j.succ = k.castSucc := rfl
      rw [heq] at hj
      exact False.elim ((not_lt_of_ge hlt.le) (hj.trans hk)))
  let b := n - a
  have hab : a + b = n := Nat.add_sub_of_le han
  let u := p ⟨a, by omega⟩
  let f := segment p 0 a (by omega)
  let g := segment p a b hab.le
  have hfH : IsChain H cap f := segment_chain hp _ _ _
  have hgH : IsChain H cap g := segment_chain hp _ _ _
  have hG : H ⊆ X := hHG.trans hGX
  have huG : u ∈ G := hHG (hp.mem _)
  have hfend : f (Fin.last a) = u := by simp [f, segment, u]
  have hgstart : g 0 = u := rfl
  have hSfront (i : Fin a) : FirstSide cap K (f i.castSucc) (f i.succ) := by
    have hh := (ha ⟨i.val, by omega⟩).mpr i.isLt
    simpa [P, f, segment] using hh
  have hSback (i : Fin b) : FirstSide (!cap) K (g i.castSucc) (g i.succ) := by
    let j : Fin n := ⟨a + i.val, by omega⟩
    have hj : ¬ P j := fun hh => (not_lt_of_ge (Nat.le_add_right _ _)) ((ha j).mp hh)
    exact (hs j).resolve_left hj
  have ha_rank : a ≤ r := by
    rw [← hrank u huG w hw]
    apply (hfH.mono hG).le_endingRank hfend
    rw [← hfend]
    exact front_eligible hSfront hw
  have hb_rank : b + r ≤ maxLength X cap := by
    rw [← hrank u huG w hw, Nat.add_comm]
    obtain ⟨q, hq, hqend, hqeligible⟩ := endingRank_attained cap (hGX huG) (slope u w)
    have hjoined := glue_chain hq (hgH.mono hG) (hqend.trans hgstart.symm) (by
      intro i j
      have hj := back_all_lt hgH hSback hw j
      rw [hgstart] at hj
      exact hj.trans_le (signed_all_of_eligible hq hqeligible i))
    exact hjoined.le_maxLength
  have hfstart : f 0 = p 0 := rfl
  have hgend : g (Fin.last b) = p (Fin.last n) := by
    change p ⟨a + b, _⟩ = p (Fin.last n)
    congr 1
    apply Fin.ext
    exact hab
  refine ⟨p 0, hp.mem _, p (Fin.last n), hp.mem _, a, b, hab.symm, ha_rank, hb_rank, ?_, ?_⟩
  · apply le_pieceLength (p := f)
    exact ⟨hfH.mono hHG, hfstart, hSfront⟩
  · apply le_pieceLength (p := g)
    exact ⟨hgH.mono hHG, hgend, hSback⟩

private theorem join_pieces {X G K : Finset Point} {cap : Bool} {m n : ℕ} {u w : Point}
    {p : Fin (m + 1) → Point} {q : Fin (n + 1) → Point}
    (hGX : G ⊆ X) (hKX : K ⊆ X) (hord : ∀ a ∈ G, ∀ b ∈ K, a.1 < b.1)
    (hp : IsPiece G K cap true u p) (hq : IsPiece K G cap false w q) :
    ∃ f : Fin (m + 1 + n + 1) → Point, IsChain X cap f ∧ f 0 = u ∧ f (Fin.last (m + 1 + n)) = w := by
  let s : Fin (m + 1 + 1) → Point := Fin.snoc p (q 0)
  have hs : IsChain X cap s := (hp.1.mono hGX).snoc (hKX (hq.1.mem 0))
    (hord _ (hp.1.mem _) _ (hq.1.mem _)) (cross_front_all_lt hp.1 hp.2.2 (hq.1.mem _))
  have hsq : s (Fin.last (m + 1)) = q 0 := by simp [s]
  refine ⟨glue s q, glue_chain hs (hq.1.mono hKX) hsq ?_, ?_, ?_⟩
  · intro i j
    apply lt_of_lt_of_le _ (hs.slopes.antitone (Fin.le_last i))
    have hj := back_all_lt hq.1 hq.2.2 (hp.1.mem (Fin.last m)) j
    rw [slope_comm (q 0)] at hj
    simpa [s] using hj
  · rw [glue_left _ _ _ (by simp)]
    simpa [s] using hp.2.1
  · rw [glue_right _ _ hsq _ (by simp)]
    trans q (Fin.last n)
    · apply congrArg q
      exact Fin.ext (by simp)
    · exact hq.2.1

/-- Section 4 on planar chains, with the geometric consequence of common cap
and cup endpoints stated as an explicit hypothesis. -/
theorem sectionFourAlternative_planar {X G₁ G₂ : Finset Point} {x₁ y₁ x₂ y₂ : ℕ}
    {height : Finset Point → ℕ}
    (hsub₁ : G₁ ⊆ X) (hsub₂ : G₂ ⊆ X) (hne₁ : G₁.Nonempty) (hne₂ : G₂.Nonempty)
    (hord : ∀ p ∈ G₁, ∀ q ∈ G₂, p.1 < q.1)
    (hr₁ : ∀ p ∈ G₁, ∀ q ∈ G₂, endingRank X true p (slope p q) = x₁ ∧
      endingRank X false p (slope p q) = y₁)
    (hr₂ : ∀ p ∈ G₁, ∀ q ∈ G₂, endingRank X true q (slope p q) = x₂ ∧
      endingRank X false q (slope p q) = y₂)
    (hs₁ : ∀ p ∈ G₁, ∀ q ∈ G₁, p.1 < q.1 → FirstSide true G₂ p q ∨ FirstSide false G₂ p q)
    (hs₂ : ∀ p ∈ G₂, ∀ q ∈ G₂, p.1 < q.1 → FirstSide true G₁ p q ∨ FirstSide false G₁ p q)
    (hpoly : ∀ {m n : ℕ} {p : Fin (m + 1) → Point} {q : Fin (n + 1) → Point},
      IsChain X true p → IsChain X false q → 0 < m → 0 < n → p 0 = q 0 →
      p (Fin.last m) = q (Fin.last n) → m + n ≤ height X)
    (η : ℝ) :
    (v X : ℝ) - ((x₂ : ℝ) + y₂ - ((x₁ : ℝ) + y₁)) - 4 * η + 2 ≤ height X ∨
    ∃ G ∈ ({G₁, G₂} : Set (Finset Point)), ∃ H ⊆ G,
      H.Nonempty ∧ G.card ≤ 2 * H.card ∧ (v H : ℝ) < (v X : ℝ) - η := by
  have hc₁ := split_planar (cap := true) hsub₁ hne₂
    (fun p hp q hq => (hr₁ p hp q hq).1) hs₁
  have hu₁ := split_planar (cap := false) hsub₁ hne₂
    (fun p hp q hq => (hr₁ p hp q hq).2) (fun p hp q hq hlt => (hs₁ p hp q hq hlt).symm)
  have hc₂ := split_planar (cap := true) hsub₂ hne₁
    (fun q hq p hp => by rw [slope_comm q p]; exact (hr₂ p hp q hq).1) hs₂
  have hu₂ := split_planar (cap := false) hsub₂ hne₁
    (fun q hq p hp => by rw [slope_comm q p]; exact (hr₂ p hp q hq).2)
    (fun p hp q hq hlt => (hs₂ p hp q hq hlt).symm)
  have hj (u : Point) (hu : u ∈ G₁) (w : Point) (hw : w ∈ G₂) :
      pieceLength G₁ G₂ true true u + pieceLength G₂ G₁ true false w +
      pieceLength G₁ G₂ false true u + pieceLength G₂ G₁ false false w + 2 ≤ height X := by
    obtain ⟨p₁, hp₁⟩ := pieceLength_attained (K := G₂) (cap := true) (front := true) hu
    obtain ⟨q₁, hq₁⟩ := pieceLength_attained (K := G₁) (cap := true) (front := false) hw
    obtain ⟨p₂, hp₂⟩ := pieceLength_attained (K := G₂) (cap := false) (front := true) hu
    obtain ⟨q₂, hq₂⟩ := pieceLength_attained (K := G₁) (cap := false) (front := false) hw
    obtain ⟨p, hp, hpstart, hpend⟩ := join_pieces hsub₁ hsub₂ hord hp₁ hq₁
    obtain ⟨q, hq, hqstart, hqend⟩ := join_pieces hsub₁ hsub₂ hord hp₂ hq₂
    have h := hpoly hp hq (by omega) (by omega) (hpstart.trans hqstart.symm) (hpend.trans hqend.symm)
    omega
  simpa [v, Nat.cast_add] using sectionFourAlternative hsub₁ hsub₂ hne₁ hne₂
    (fun _ _ h => maxLength_mono h true) (fun _ _ h => maxLength_mono h false)
    hc₁ hu₁ hc₂ hu₂ hj η

end ESVerify
