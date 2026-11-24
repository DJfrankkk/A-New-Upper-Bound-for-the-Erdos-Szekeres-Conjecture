import ESVerify.Planar

set_option autoImplicit false

namespace ESVerify

/-- A threshold forcing a convex `n`-point subset in every sufficiently large set. -/
def IsESBound (n m : ℕ) : Prop :=
  ∀ P : Finset Point, GeneralPosition P → m ≤ P.card →
    ∃ Q ⊆ P, ConvexPosition Q ∧ Q.card = n

theorem isESBound_iff_card_eq {n m : ℕ} :
    IsESBound n m ↔ ∀ P : Finset Point, GeneralPosition P → P.card = m →
      ∃ Q ⊆ P, ConvexPosition Q ∧ Q.card = n := by
  constructor
  · intro hb P hP hcard
    exact hb P hP hcard.ge
  · intro hb P hP hcard
    obtain ⟨S, hSP, hScard⟩ := Finset.exists_subset_card_eq hcard
    have hS : GeneralPosition S := by
      intro p hp q hq r hr
      exact hP p (hSP hp) q (hSP hq) r (hSP hr)
    obtain ⟨Q, hQS, hQ, hQcard⟩ := hb S hS hScard
    exact ⟨Q, hQS.trans hSP, hQ, hQcard⟩

/-- The Erdős–Szekeres number. Its threshold property is proved below. -/
noncomputable def esNumber (n : ℕ) : ℕ := sInf {m | IsESBound n m}

private theorem height_attained (P : Finset Point) :
    ∃ Q ⊆ P, ConvexPosition Q ∧ Q.card = h P := by
  have hmem : h P ∈ {n : ℕ | n = 0 ∨ ∃ Q ⊆ P, ConvexPosition Q ∧ Q.card = n} := by
    apply Nat.sSup_mem
    · exact ⟨0, Or.inl rfl⟩
    · refine ⟨P.card, ?_⟩
      rintro n (rfl | ⟨Q, hQP, _, rfl⟩)
      · exact Nat.zero_le _
      · exact Finset.card_le_card hQP
  rcases hmem with he | hq
  · exact ⟨∅, Finset.empty_subset _, by simp [ConvexPosition], by simpa using he.symm⟩
  · exact hq

private theorem exists_convex_subset_of_le_h {P : Finset Point} {n : ℕ} (hn : n ≤ h P) :
    ∃ Q ⊆ P, ConvexPosition Q ∧ Q.card = n := by
  obtain ⟨S, hSP, hS, hScard⟩ := height_attained P
  obtain ⟨Q, hQS, hQcard⟩ := Finset.exists_subset_card_eq (show n ≤ S.card by rwa [hScard])
  refine ⟨Q, hQS.trans hSP, ?_, hQcard⟩
  intro p hp hmem
  apply hS p (hQS hp)
  have hsub : ((Q : Set Point) \ {p}) ⊆ ((S : Set Point) \ {p}) := by
    intro a ha
    exact ⟨hQS ha.1, ha.2⟩
  exact convexHull_mono hsub hmem

/-- The threshold formulation of the consequence in Theorem 1.1,
with an explicit increase of the constant to allow integer rounding. -/
theorem esNumber_bound_of_log_height
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point, P.Nonempty → GeneralPosition P →
      Real.logb 2 P.card ≤ h P + C * (h P : ℝ) ^ (1 / 3 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      IsESBound n (esNumber n) ∧
        (esNumber n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + C * (n : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := hbound
  refine ⟨C + 1, by positivity, ?_⟩
  intro n hn
  let u : ℝ := n + C * (n : ℝ) ^ (1 / 3 : ℝ)
  let a : ℝ := (2 : ℝ) ^ u
  let m : ℕ := ⌈a⌉₊
  have hua : (0 : ℝ) ≤ u := by unfold u; positivity
  have ha : 1 ≤ a := Real.one_le_rpow (by norm_num) hua
  have ham : a ≤ (m : ℝ) := Nat.le_ceil _
  have hm : IsESBound n m := by
    intro P hPgp hPm
    have hPma : a ≤ (P.card : ℝ) := ham.trans (by exact_mod_cast hPm)
    have hPpos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by linarith) hPma
    have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hPpos)
    apply exists_convex_subset_of_le_h
    by_contra! hsmall
    have hlog := (Real.strictMonoOn_logb (show (1 : ℝ) < 2 by norm_num)).monotoneOn
      (show 0 < a by linarith) hPpos hPma
    have hlog' : u ≤ Real.logb 2 P.card := by
      unfold a at hlog
      rwa [Real.logb_rpow (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 1)] at hlog
    have hsmall' : (h P : ℝ) < n := by exact_mod_cast hsmall
    have hpow : (h P : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hsmall'.le (by norm_num)
    have hc := mul_le_mul_of_nonneg_left hpow hC.le
    have hboundP := hb P hP hPgp
    dsimp [u] at hlog'
    linarith
  have hnonempty : {m : ℕ | IsESBound n m}.Nonempty := ⟨m, hm⟩
  have hes : esNumber n ≤ m := Nat.sInf_le hm
  refine ⟨Nat.sInf_mem hnonempty, ?_⟩
  have hnp : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpow : 1 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hnp (by norm_num)
  calc
    (esNumber n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hes
    _ ≤ a + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ a)).le
    _ ≤ a * 2 := by linarith
    _ = (2 : ℝ) ^ (u + 1) := (Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0) u).symm
    _ ≤ (2 : ℝ) ^ ((n : ℝ) + (C + 1) * (n : ℝ) ^ (1 / 3 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      dsimp [u]
      linarith

end ESVerify
