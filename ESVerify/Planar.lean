import Mathlib

/-! The plane, chains, ending ranks and convex position in Section 2. -/

noncomputable section

namespace ESVerify

abbrev Point := ℝ × ℝ

def slope (p q : Point) : ℝ := (q.2 - p.2) / (q.1 - p.1)

def orientation (p q r : Point) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

def GeneralPosition (X : Finset Point) : Prop :=
  ∀ p ∈ X, ∀ q ∈ X, ∀ r ∈ X, p ≠ q → p ≠ r → q ≠ r →
    orientation p q r ≠ 0

def DistinctAbscissae (X : Finset Point) : Prop :=
  Set.InjOn Prod.fst (X : Set Point)

theorem slope_ne_of_generalPosition {X : Finset Point} (hg : GeneralPosition X)
    {p q r : Point} (hp : p ∈ X) (hq : q ∈ X) (hr : r ∈ X)
    (hpq : p.1 < q.1) (hqr : q.1 < r.1) :
    slope p q ≠ slope q r := by
  have hpq' : p ≠ q := fun h => (ne_of_lt hpq) (congrArg Prod.fst h)
  have hpr' : p ≠ r := fun h => (ne_of_lt (hpq.trans hqr)) (congrArg Prod.fst h)
  have hqr' : q ≠ r := fun h => (ne_of_lt hqr) (congrArg Prod.fst h)
  intro hs
  apply hg p hp q hq r hr hpq' hpr' hqr'
  unfold slope at hs
  field_simp [ne_of_gt (sub_pos.mpr hpq), ne_of_gt (sub_pos.mpr hqr)] at hs
  unfold orientation
  nlinarith only [hs]

/-- Reflecting the vertical coordinate exchanges caps and cups. -/
def signed (cap : Bool) (y : ℝ) : ℝ := if cap then y else -y

@[simp] theorem signed_true (x : ℝ) : signed true x = x := rfl
@[simp] theorem signed_false (x : ℝ) : signed false x = -x := rfl

def edgeSlope {n : ℕ} (p : Fin (n + 1) → Point) (i : Fin n) : ℝ :=
  slope (p i.castSucc) (p i.succ)

structure IsChain (X : Finset Point) (cap : Bool) {n : ℕ}
    (p : Fin (n + 1) → Point) : Prop where
  mem : ∀ i, p i ∈ X
  ordered : StrictMono fun i => (p i).1
  slopes : StrictAnti fun i => signed cap (edgeSlope p i)

theorem IsChain.mono {X Y : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) (hXY : X ⊆ Y) :
    IsChain Y cap p :=
  ⟨fun i => hXY (hp.mem i), hp.ordered, hp.slopes⟩

theorem IsChain.injective {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) :
    Function.Injective p :=
  fun _ _ h => hp.ordered.injective (congrArg Prod.fst h)

theorem IsChain.length_add_one_le_card {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) :
    n + 1 ≤ X.card := by
  classical
  let f : Fin (n + 1) → ↥X := fun i => ⟨p i, hp.mem i⟩
  have hf : Function.Injective f := fun _ _ h =>
    hp.injective (congrArg Subtype.val h)
  simpa using Fintype.card_le_of_injective f hf

theorem singleton_chain {X : Finset Point} {cap : Bool} {p : Point} (hp : p ∈ X) :
    IsChain X cap (n := 0) (fun _ => p) := by
  constructor
  · exact fun _ => hp
  · intro i j hij
    omega
  · intro i
    exact Fin.elim0 i

def maxLength (X : Finset Point) (cap : Bool) : ℕ :=
  sSup {n : ℕ | n = 0 ∨ ∃ p : Fin (n + 1) → Point, IsChain X cap p}

theorem IsChain.le_maxLength {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) : n ≤ maxLength X cap := by
  apply le_csSup
  · refine ⟨X.card, ?_⟩
    rintro n (rfl | ⟨p, h⟩)
    · exact Nat.zero_le _
    · exact h.length_add_one_le_card.trans' (Nat.le_succ _)
  · exact Or.inr ⟨p, hp⟩

theorem maxLength_attained {X : Finset Point} (hX : X.Nonempty) (cap : Bool) :
    ∃ p : Fin (maxLength X cap + 1) → Point, IsChain X cap p := by
  have hmem :
      maxLength X cap ∈ {n : ℕ | n = 0 ∨ ∃ p : Fin (n + 1) → Point, IsChain X cap p} := by
    apply Nat.sSup_mem
    · exact ⟨0, Or.inl rfl⟩
    · refine ⟨X.card, ?_⟩
      rintro n (rfl | ⟨p, h⟩)
      · exact Nat.zero_le _
      · exact h.length_add_one_le_card.trans' (Nat.le_succ _)
  rcases hmem with h0 | h
  · rw [h0]
    obtain ⟨p, hp⟩ := hX
    exact ⟨fun _ => p, singleton_chain hp⟩
  · exact h

theorem maxLength_mono {X Y : Finset Point} (hXY : X ⊆ Y) (cap : Bool) :
    maxLength X cap ≤ maxLength Y cap := by
  refine csSup_le (α := ℕ) ⟨0, Or.inl rfl⟩ ?_
  rintro n (rfl | ⟨p, hp⟩)
  · exact Nat.zero_le _
  · exact (hp.mono hXY).le_maxLength

def LastEdgeEligible (cap : Bool) :
    {n : ℕ} → (Fin (n + 1) → Point) → ℝ → Prop
  | 0, _, _ => True
  | n + 1, p, t => signed cap t ≤ signed cap (edgeSlope p (Fin.last n))

def endingRank (X : Finset Point) (cap : Bool) (q : Point) (t : ℝ) : ℕ :=
  sSup {n : ℕ | n = 0 ∨ ∃ p : Fin (n + 1) → Point,
    IsChain X cap p ∧ p (Fin.last n) = q ∧ LastEdgeEligible cap p t}

theorem IsChain.le_endingRank {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) {q : Point} (hend : p (Fin.last n) = q)
    {t : ℝ} (ht : LastEdgeEligible cap p t) : n ≤ endingRank X cap q t := by
  apply le_csSup
  · refine ⟨maxLength X cap, ?_⟩
    rintro m (rfl | ⟨f, hf, _, _⟩)
    · exact Nat.zero_le _
    · exact hf.le_maxLength
  · exact Or.inr ⟨p, hp, hend, ht⟩

theorem endingRank_le_maxLength (X : Finset Point) (cap : Bool) (q : Point) (t : ℝ) :
    endingRank X cap q t ≤ maxLength X cap := by
  refine csSup_le (α := ℕ) ⟨0, Or.inl rfl⟩ ?_
  rintro n (rfl | ⟨p, hp, _, _⟩)
  · exact Nat.zero_le _
  · exact hp.le_maxLength

theorem endingRank_attained {X : Finset Point} (cap : Bool) {q : Point}
    (hq : q ∈ X) (t : ℝ) :
    ∃ p : Fin (endingRank X cap q t + 1) → Point,
      IsChain X cap p ∧ p (Fin.last (endingRank X cap q t)) = q ∧ LastEdgeEligible cap p t := by
  have hmem : endingRank X cap q t ∈
      {n : ℕ | n = 0 ∨ ∃ p : Fin (n + 1) → Point,
        IsChain X cap p ∧ p (Fin.last n) = q ∧ LastEdgeEligible cap p t} := by
    apply Nat.sSup_mem
    · exact ⟨0, Or.inl rfl⟩
    · refine ⟨maxLength X cap, ?_⟩
      rintro n (rfl | ⟨p, hp, _, _⟩)
      · exact Nat.zero_le _
      · exact hp.le_maxLength
  rcases hmem with h0 | h
  · rw [h0]
    exact ⟨fun _ => q, singleton_chain hq, rfl, trivial⟩
  · exact h

theorem LastEdgeEligible.mono {cap : Bool} {n : ℕ} {p : Fin (n + 1) → Point}
    {s t : ℝ} (hst : signed cap s ≤ signed cap t) (ht : LastEdgeEligible cap p t) :
    LastEdgeEligible cap p s := by
  cases n with
  | zero => exact trivial
  | succ n => exact hst.trans ht

theorem endingRank_le_of_signed_le (X : Finset Point) (cap : Bool) (q : Point)
    {s t : ℝ} (hst : signed cap s ≤ signed cap t) :
    endingRank X cap q t ≤ endingRank X cap q s := by
  refine csSup_le (α := ℕ) ⟨0, Or.inl rfl⟩ ?_
  rintro n (rfl | ⟨p, hp, hend, ht⟩)
  · exact Nat.zero_le _
  · exact hp.le_endingRank hend (ht.mono hst)

theorem endingRank_cap_antitone (X : Finset Point) (q : Point) :
    Antitone (endingRank X true q) :=
  fun _ _ hst => endingRank_le_of_signed_le X true q hst

theorem endingRank_cup_monotone (X : Finset Point) (q : Point) :
    Monotone (endingRank X false q) :=
  fun _ _ hst => endingRank_le_of_signed_le X false q (neg_le_neg hst)

def v (X : Finset Point) : ℕ := maxLength X true + maxLength X false

theorem v_mono {X Y : Finset Point} (hXY : X ⊆ Y) : v X ≤ v Y :=
  Nat.add_le_add (maxLength_mono hXY true) (maxLength_mono hXY false)

@[simp] theorem edgeSlope_snoc_castSucc {n : ℕ} (p : Fin (n + 1) → Point)
    (q : Point) (i : Fin n) : edgeSlope (Fin.snoc p q) i.castSucc = edgeSlope p i := by
  simp only [edgeSlope, Fin.snoc_castSucc, Fin.succ_castSucc]

@[simp] theorem edgeSlope_snoc_last {n : ℕ} (p : Fin (n + 1) → Point) (q : Point) :
    edgeSlope (Fin.snoc p q) (Fin.last n) = slope (p (Fin.last n)) q := by
  simp [edgeSlope, Fin.succ_last]

theorem IsChain.snoc {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) {q : Point} (hq : q ∈ X)
    (hord : (p (Fin.last n)).1 < q.1)
    (hs : ∀ i : Fin n, signed cap (slope (p (Fin.last n)) q) <
      signed cap (edgeSlope p i)) :
    IsChain X cap (Fin.snoc p q) := by
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hq
    · simpa using hp.mem j
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Fin.succ_last] using hord
    · simpa only [Fin.succ_castSucc, Fin.snoc_castSucc] using hp.ordered (Fin.castSucc_lt_succ (i := j))
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · intro h
      exact False.elim ((not_lt_of_ge (Fin.le_last j)) h)
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro _
        simpa using hs i'
      · intro hij
        simpa using hp.slopes (show i' < j' from hij)

theorem endingRank_grows {X : Finset Point} (hgp : GeneralPosition X) (cap : Bool)
    {p q : Point} (hp : p ∈ X) (hq : q ∈ X) (hpq : p.1 < q.1) :
    endingRank X cap p (slope p q) + 1 ≤ endingRank X cap q (slope p q) := by
  obtain ⟨f, hf, hlast, ht⟩ := endingRank_attained cap hp (slope p q)
  generalize hn : endingRank X cap p (slope p q) = n at f hf hlast ht ⊢
  have hs : ∀ i : Fin n, signed cap (slope p q) < signed cap (edgeSlope f i) := by
    cases n with
    | zero => intro i; exact Fin.elim0 i
    | succ k =>
      intro i
      apply lt_of_lt_of_le _ (hf.slopes.antitone (Fin.le_last i))
      have hx : (f (Fin.last k).castSucc).1 < (f (Fin.last k).succ).1 :=
        hf.ordered (Fin.castSucc_lt_succ (i := Fin.last k))
      have hend : f (Fin.last k).succ = p := by simpa [Fin.succ_last] using hlast
      have hy : (f (Fin.last k).castSucc).1 < p.1 := by rwa [hend] at hx
      have hne : edgeSlope f (Fin.last k) ≠ slope p q := by
        rw [edgeSlope, hend]
        exact slope_ne_of_generalPosition hgp (hf.mem _) hp hq hy hpq
      refine lt_of_le_of_ne ht ?_
      cases cap <;> simpa using Ne.symm hne
  have hc := hf.snoc hq (by rw [hlast]; exact hpq) (by simpa [hlast] using hs)
  apply hc.le_endingRank (by simp)
  change signed cap (slope p q) ≤ signed cap (edgeSlope (Fin.snoc f q) (Fin.last n))
  simp [hlast]

/-- Every point of the finite set is a vertex of its convex hull. -/
def ConvexPosition (X : Finset Point) : Prop :=
  ∀ p ∈ X, p ∉ convexHull ℝ ((X : Set Point) \ {p})

def h (X : Finset Point) : ℕ :=
  sSup {n : ℕ | n = 0 ∨ ∃ S ⊆ X, ConvexPosition S ∧ S.card = n}

theorem ConvexPosition.card_le_h {X S : Finset Point} (hS : ConvexPosition S)
    (hSX : S ⊆ X) : S.card ≤ h X := by
  apply le_csSup
  · refine ⟨X.card, ?_⟩
    rintro n (rfl | ⟨S, hSX, _, rfl⟩)
    · exact Nat.zero_le _
    · exact Finset.card_le_card hSX
  · exact Or.inr ⟨S, hSX, hS, rfl⟩

theorem h_mono {X Y : Finset Point} (hXY : X ⊆ Y) : h X ≤ h Y := by
  refine csSup_le (α := ℕ) ⟨0, Or.inl rfl⟩ ?_
  rintro n (rfl | ⟨S, hSX, hS, rfl⟩)
  · exact Nat.zero_le _
  · exact hS.card_le_h (hSX.trans hXY)

theorem one_le_h {X : Finset Point} (hX : X.Nonempty) : 1 ≤ h X := by
  obtain ⟨p, hp⟩ := hX
  have hpc : ConvexPosition {p} := by simp [ConvexPosition]
  simpa using hpc.card_le_h (Finset.singleton_subset_iff.mpr hp)

private theorem lt_values_of_adjacent {n : ℕ} (f : Fin (n + 1) → ℝ)
    {i j : Fin (n + 1)} (hij : i < j)
    (hf : ∀ k : Fin n, i.val ≤ k.val → k.val < j.val → f k.castSucc < f k.succ) :
    f i < f j := by
  let d := j.val - i.val
  have hij' : i.val < j.val := hij
  have hd : i.val + d = j.val := by dsimp [d]; omega
  let g : Fin (d + 1) → ℝ := fun k => f ⟨i.val + k.val, by omega⟩
  have hmono : StrictMono g := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    have hk : k.val < d := k.isLt
    let l : Fin n := ⟨i.val + k.val, by omega⟩
    exact hf l (by dsimp [l]; omega) (by dsimp [l]; omega)
  have h0 : (0 : Fin (d + 1)) < Fin.last d := by
    change 0 < d
    omega
  have ha : (⟨i.val + (0 : Fin (d + 1)).val, by simpa using i.isLt⟩ : Fin (n + 1)) = i :=
    Fin.ext (by simp)
  have hb : (⟨i.val + (Fin.last d).val, by simpa [hd] using j.isLt⟩ : Fin (n + 1)) = j :=
    Fin.ext (by simp [hd])
  simpa only [g, ha, hb] using hmono h0

/-- The slope of a line strictly supporting a vertex lies between the incident slopes. -/
private theorem IsChain.exists_supportSlope {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) (i : Fin (n + 1)) :
    ∃ m : ℝ,
      (∀ j : Fin n, j.val < i.val → m < signed cap (edgeSlope p j)) ∧
      (∀ j : Fin n, i.val ≤ j.val → signed cap (edgeSlope p j) < m) := by
  by_cases hi : i.val = 0
  · by_cases hn : n = 0
    · subst n
      exact ⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    · let j₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      refine ⟨signed cap (edgeSlope p j₀) + 1, ?_, ?_⟩
      · intro j hj
        omega
      · intro j _
        apply lt_of_le_of_lt (hp.slopes.antitone (show j₀ ≤ j from Nat.zero_le _))
        linarith
  · let l : Fin n := ⟨i.val - 1, by omega⟩
    by_cases hl : i.val = n
    · refine ⟨signed cap (edgeSlope p l) - 1, ?_, ?_⟩
      · intro j hj
        apply lt_of_lt_of_le _ (hp.slopes.antitone (show j ≤ l by change j.val ≤ i.val - 1; omega))
        linarith
      · intro j hj
        omega
    · let r : Fin n := ⟨i.val, by omega⟩
      have hlr : l < r := by change i.val - 1 < i.val; omega
      have hs := hp.slopes hlr
      refine ⟨(signed cap (edgeSlope p l) + signed cap (edgeSlope p r)) / 2, ?_, ?_⟩
      · intro j hj
        apply lt_of_lt_of_le _ (hp.slopes.antitone (show j ≤ l by change j.val ≤ i.val - 1; omega))
        linarith
      · intro j hj
        apply lt_of_le_of_lt (hp.slopes.antitone (show r ≤ j from hj))
        linarith

/-- The value of the supporting affine functional associated to slope `m`. -/
def supportValue (cap : Bool) (m : ℝ) (p : Point) : ℝ := signed cap p.2 - m * p.1

private theorem IsChain.supportValue_sub {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) (k : Fin n) (m : ℝ) :
    supportValue cap m (p k.succ) - supportValue cap m (p k.castSucc) =
      (signed cap (edgeSlope p k) - m) * ((p k.succ).1 - (p k.castSucc).1) := by
  have hx := hp.ordered (Fin.castSucc_lt_succ (i := k))
  have hne := ne_of_gt (sub_pos.mpr hx)
  cases cap <;> simp only [supportValue, signed_true, signed_false, edgeSlope, slope] <;>
    field_simp <;> ring

theorem IsChain.supports {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) (i : Fin (n + 1)) :
    ∃ m : ℝ, ∀ j : Fin (n + 1), j ≠ i → supportValue cap m (p j) < supportValue cap m (p i) := by
  obtain ⟨m, hl, hr⟩ := hp.exists_supportSlope i
  refine ⟨m, fun j hji => ?_⟩
  rcases lt_or_gt_of_ne hji with hj | hj
  · apply lt_values_of_adjacent (fun k => supportValue cap m (p k)) hj
    intro k _ hk
    apply sub_pos.mp
    rw [hp.supportValue_sub]
    exact mul_pos (sub_pos.mpr (hl k hk))
      (sub_pos.mpr (hp.ordered (Fin.castSucc_lt_succ (i := k))))
  · have hlt : -supportValue cap m (p i) < -supportValue cap m (p j) := by
      apply lt_values_of_adjacent (fun k => -supportValue cap m (p k)) hj
      intro k hk _
      apply neg_lt_neg
      apply sub_neg.mp
      rw [hp.supportValue_sub]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr (hr k hk))
        (sub_pos.mpr (hp.ordered (Fin.castSucc_lt_succ (i := k))))
    exact neg_lt_neg_iff.mp hlt

theorem convex_supportValue_lt (cap : Bool) (m z : ℝ) :
    Convex ℝ {p : Point | supportValue cap m p < z} := by
  apply convex_halfSpace_lt
  constructor
  · intro p q
    cases cap <;> simp [supportValue] <;> ring
  · intro a p
    cases cap <;> simp [supportValue, smul_eq_mul] <;> ring

theorem convexPosition_of_support {S : Finset Point}
    (hs : ∀ p ∈ S, ∃ (cap : Bool) (m : ℝ), ∀ q ∈ S, q ≠ p →
      supportValue cap m q < supportValue cap m p) : ConvexPosition S := by
  intro p hp hmem
  obtain ⟨cap, m, hm⟩ := hs p hp
  have hsub : (S : Set Point) \ {p} ⊆
      {q : Point | supportValue cap m q < supportValue cap m p} :=
    fun q hq => hm q hq.1 hq.2
  have hh : p ∈ {q : Point | supportValue cap m q < supportValue cap m p} :=
    convexHull_min hsub (convex_supportValue_lt _ _ _) hmem
  exact (lt_irrefl (supportValue cap m p)) hh

noncomputable def vertices {n : ℕ} (p : Fin (n + 1) → Point) : Finset Point :=
  Finset.univ.image p

theorem IsChain.vertices_subset {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) : vertices p ⊆ X := by
  classical
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact hp.mem i

theorem IsChain.card_vertices {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) : (vertices p).card = n + 1 := by
  classical
  unfold vertices
  rw [Finset.card_image_of_injective _ hp.injective]
  simp

theorem IsChain.vertices_convexPosition {X : Finset Point} {cap : Bool} {n : ℕ}
    {p : Fin (n + 1) → Point} (hp : IsChain X cap p) : ConvexPosition (vertices p) := by
  classical
  apply convexPosition_of_support
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨m, hm⟩ := hp.supports i
  refine ⟨cap, m, ?_⟩
  intro y hy hye
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  exact hm j (fun h => hye (congrArg p h))

theorem maxLength_add_one_le_h {X : Finset Point} (hX : X.Nonempty) (cap : Bool) :
    maxLength X cap + 1 ≤ h X := by
  obtain ⟨p, hp⟩ := maxLength_attained hX cap
  simpa [hp.card_vertices] using hp.vertices_convexPosition.card_le_h hp.vertices_subset

theorem v_add_two_le_two_mul_h {X : Finset Point} (hX : X.Nonempty) :
    v X + 2 ≤ 2 * h X := by
  have hc := maxLength_add_one_le_h hX true
  have hu := maxLength_add_one_le_h hX false
  unfold v
  omega

end ESVerify