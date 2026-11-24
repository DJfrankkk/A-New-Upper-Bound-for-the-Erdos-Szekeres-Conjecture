import ESVerify.EnergyApproximation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fin.Tuple.Basic

/-! The cosine eigenfunction estimate for the killed walk in Lemma 6.1. -/

open scoped BigOperators

namespace ESVerify

private def intStep (b : Bool) : ℤ := if b then 1 else -1

private theorem signHeight_cons_succ {v k : ℕ} (b : Bool) (w : SignWord v) :
    signHeight (Fin.cons b w) (k+1) = intStep b + signHeight w k := by
  unfold signHeight
  rw [Finset.sum_range_succ', add_comm]
  have hzero : atIndex (fun j : Fin (v+1) => if Fin.cons (α := fun _ => Bool) b w j then (1 : ℤ) else -1) 0 =
      intStep b := by simp [atIndex, intStep]
  rw [hzero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i < v
  · have hs : i+1 < v+1 := Nat.succ_lt_succ h
    rw [atIndex_of_lt _ hs, atIndex_of_lt _ h]
    have heq : (⟨i+1, hs⟩ : Fin (v+1)) = (⟨i, h⟩ : Fin v).succ := Fin.ext rfl
    rw [heq, Fin.cons_succ]
  · have hs : ¬ i+1 < v+1 := by omega
    simp [atIndex, h, hs]

private def stays {v : ℕ} (d : ℕ) (x : ℤ) (w : SignWord v) : Prop :=
  ∀ k : ℕ, k ≤ v → |x + signHeight w k| ≤ (d : ℤ)

private theorem stays_cons {v d : ℕ} (x : ℤ) (hx : |x| ≤ (d : ℤ))
    (b : Bool) (w : SignWord v) :
    stays d x (Fin.cons b w) ↔ stays d (x + intStep b) w := by
  constructor
  · intro h k hk
    simpa only [signHeight_cons_succ, add_assoc] using h (k+1) (by omega)
  · intro h k hk
    cases k with
    | zero => simpa [signHeight] using hx
    | succ k => simpa only [signHeight_cons_succ, add_assoc] using h k (by omega)

private noncomputable def angle (d : ℕ) : ℝ := Real.pi / (2 * ((d : ℝ) + 1))

private noncomputable def weightedWalk (v d : ℕ) (x : ℤ) : ℝ := by
  classical
  exact ∑ w : SignWord v, if stays d x w then Real.cos (angle d * ((x + signHeight w v : ℤ) : ℝ)) else 0

private theorem weightedWalk_succ (v d : ℕ) (x : ℤ) (hx : |x| ≤ (d : ℤ)) :
    weightedWalk (v+1) d x = weightedWalk v d (x+1) + weightedWalk v d (x-1) := by
  classical
  let f (w : SignWord (v+1)) : ℝ :=
    if stays d x w then Real.cos (angle d * ((x + signHeight w (v+1) : ℤ) : ℝ)) else 0
  have heq : (∑ w : SignWord (v+1), f w) = ∑ p : Bool × SignWord v, f (Fin.cons p.1 p.2) := by
    symm
    exact Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (v+1) => Bool) _ _ (fun _ => rfl)
  change (∑ w : SignWord (v+1), f w) = _
  rw [heq, Fintype.sum_prod_type]
  simp only [f, stays_cons x hx, signHeight_cons_succ, ← add_assoc, Fintype.sum_bool,
    intStep, Bool.false_eq_true, ↓reduceIte, sub_eq_add_neg]
  rfl

private theorem cosine_boundary (d : ℕ) (x : ℤ) (hx : |x| ≤ (d : ℤ)+1) :
    (if |x| ≤ (d : ℤ) then Real.cos (angle d * (x : ℝ)) else 0) =
      Real.cos (angle d * (x : ℝ)) := by
  split
  · rfl
  · rename_i hn
    rw [abs_le] at hx hn
    have hd : (d : ℝ) + 1 ≠ 0 := by positivity
    have hb : angle d * ((d : ℝ)+1) = Real.pi/2 := by
      unfold angle
      field_simp
    have hcases : x = (d : ℤ)+1 ∨ x = -((d : ℤ)+1) := by omega
    rcases hcases with rfl | rfl
    · push_cast
      rw [hb, Real.cos_pi_div_two]
    · push_cast
      rw [mul_neg, Real.cos_neg, hb, Real.cos_pi_div_two]

private theorem weightedWalk_eq (v d : ℕ) (x : ℤ) :
    weightedWalk v d x = if |x| ≤ (d : ℤ) then
      (2 * Real.cos (angle d))^v * Real.cos (angle d * (x : ℝ)) else 0 := by
  classical
  induction v generalizing x with
  | zero =>
    simp [weightedWalk, stays, signHeight]
  | succ v ih =>
    by_cases hx : |x| ≤ (d : ℤ)
    · rw [weightedWalk_succ _ _ _ hx, ih, ih, if_pos hx, pow_succ]
      have hxp : |x+1| ≤ (d : ℤ)+1 := by rw [abs_le] at hx ⊢; omega
      have hxm : |x-1| ≤ (d : ℤ)+1 := by rw [abs_le] at hx ⊢; omega
      have hfactor (y : ℤ) (hy : |y| ≤ (d : ℤ)+1) :
          (if |y| ≤ (d : ℤ) then (2 * Real.cos (angle d))^v *
            Real.cos (angle d * (y : ℝ)) else 0) =
              (2 * Real.cos (angle d))^v * Real.cos (angle d * (y : ℝ)) := by
        rw [← cosine_boundary d y hy]
        split <;> simp_all
      rw [hfactor _ hxp, hfactor _ hxm, ← mul_add, Real.cos_add_cos]
      push_cast
      have heq₁ : (angle d * ((x : ℝ)+1) + angle d * ((x : ℝ)-1))/2 = angle d * x := by ring
      have heq₂ : (angle d * ((x : ℝ)+1) - angle d * ((x : ℝ)-1))/2 = angle d := by ring
      rw [heq₁, heq₂]
      ring
    · rw [if_neg hx]
      unfold weightedWalk
      apply Finset.sum_eq_zero
      intro w _
      apply if_neg
      intro h
      exact hx (by simpa [signHeight] using h 0 (Nat.zero_le _))

private theorem exp_neg_eight_div_le_cos {d : ℕ} (hd : 0 < d) :
    Real.exp (-8/(d : ℝ)^2) ≤ Real.cos (angle d) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hangle_nonneg : 0 ≤ angle d := by unfold angle; positivity
  have hangle_mul : angle d * (d + 1) = Real.pi / 2 := by
    unfold angle
    field_simp
  have hangle_le : angle d ≤ 1 := by
    nlinarith [Real.pi_lt_four, mul_nonneg hangle_nonneg (sub_nonneg.mpr hd')]
  have hangle_d : angle d * d ≤ 2 := by linarith [Real.pi_lt_four]
  have hsq : angle d ^ 2 ≤ 8/(d : ℝ)^2 := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ = (angle d * d)^2 := by ring
      _ ≤ 2^2 := by gcongr
      _ ≤ 8 := by norm_num
  calc
    _ ≤ Real.exp (-(angle d)^2) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hsq
    _ ≤ 1 - (angle d)^2 / 2 := by
      rw [Real.exp_neg, ← one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).2
      have hs : (angle d)^2 ≤ 1 := by simpa using (pow_le_pow_left₀ hangle_nonneg hangle_le 2)
      calc
        (1 : ℝ) ≤ (1 - (angle d)^2/2) * (1 + (angle d)^2) := by
          nlinarith [mul_nonneg (sq_nonneg (angle d)) (sub_nonneg.mpr hs)]
        _ ≤ (1 - (angle d)^2/2) * Real.exp ((angle d)^2) := by
          gcongr
          · linarith
          · rw [add_comm]
            exact Real.add_one_le_exp _
    _ ≤ Real.cos (angle d) := Real.one_sub_sq_div_two_le_cos

/-- Survival in the strip has probability at least `exp(-8*v/d²)`, as used in §6.1. -/
theorem killedWalkEstimate : KilledWalkEstimate := by
  classical
  intro v d hd
  have hstay (w : SignWord v) : stays d 0 w ↔ w ∈ stripWords v d := by
    simp only [stripWords, Finset.mem_filter, Finset.mem_univ, true_and, stays, zero_add,
      ← signHeight_cast]
    constructor <;> intro h k hk <;> exact_mod_cast h k hk
  have hcard : weightedWalk v d 0 ≤ ((stripWords v d).card : ℝ) := by
    unfold weightedWalk
    rw [show ((stripWords v d).card : ℝ) = ∑ _w ∈ stripWords v d, (1 : ℝ) by simp]
    rw [← Finset.sum_filter]
    have heq : ({w ∈ (Finset.univ : Finset (SignWord v)) | stays d 0 w} : Finset (SignWord v)) =
        stripWords v d := by ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hstay]
    rw [heq]
    apply Finset.sum_le_sum
    intro w _
    exact Real.cos_le_one _
  have hm : weightedWalk v d 0 = (2 * Real.cos (angle d))^v := by
    rw [weightedWalk_eq]
    simp
  rw [hm, mul_pow] at hcard
  unfold cubeMeasure
  calc
    _ = (Real.exp (-8/(d : ℝ)^2))^v := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ (Real.cos (angle d))^v := by
      exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_eight_div_le_cos hd) _
    _ ≤ _ := (le_div_iff₀ (by positivity)).2 (by simpa [mul_comm] using hcard)

end ESVerify
