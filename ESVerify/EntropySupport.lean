import ESVerify.EnergyApproximation
import Mathlib.Data.Nat.Log

set_option autoImplicit false

open scoped BigOperators

namespace ESVerify

theorem energy_eq_of_le {v : ℕ} (a : Fin v → ℝ) {n : ℕ} (h : v ≤ n) :
    energy a n = energy a v := by
  unfold energy
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro i _ hi
  simp [atIndex, show ¬ i < v from fun hv ↦ hi (Finset.mem_range.mpr hv)]

/-- Total variation through an integer time, including zero increments after the path ends. -/
def variation {v : ℕ} (a : Fin v → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, |atIndex a i|

theorem variation_eq_of_le {v : ℕ} (a : Fin v → ℝ) {n : ℕ} (h : v ≤ n) :
    variation a n = variation a v := by
  unfold variation
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro i _ hi
  simp [atIndex, show ¬ i < v from fun hv ↦ hi (Finset.mem_range.mpr hv)]

theorem variation_bound {v : ℕ} (a : Fin v → ℝ) {n : ℕ} (h : v ≤ n) :
    variation a n ≤ Real.sqrt ((v : ℝ) * energy a v) := by
  rw [variation_eq_of_le a h]
  have hsq : variation a v ^ 2 ≤ (v : ℝ) * energy a v := by
    simpa [variation, energy, sq_abs] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range v) (fun _ ↦ (1 : ℝ))
        (fun i ↦ |atIndex a i|))
  have hnon : 0 ≤ (v : ℝ) * energy a v := mul_nonneg (Nat.cast_nonneg _) (energy_nonneg a v)
  exact (Real.le_sqrt (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hnon).mpr hsq

theorem pathHeight_differences {v : ℕ} (H : ℕ → ℝ) {k : ℕ} (hk : k ≤ v) :
    pathHeight (fun i : Fin v ↦ H (i.val + 1) - H i.val) k = H k - H 0 := by
  induction k with
  | zero => simp [pathHeight]
  | succ k ih =>
    have hkv : k < v := hk
    unfold pathHeight at ih ⊢
    rw [Finset.sum_range_succ, ih hkv.le, atIndex_of_lt _ hkv]
    simp

theorem exists_dyadicLength {v : ℕ} (hv : 0 < v) :
    ∃ n : ℕ, v ≤ 2 ^ n ∧ 2 ^ n ≤ 2 * v := by
  by_cases h : v = 1
  · exact ⟨0, by simp [h], by simp [h]⟩
  let n := Nat.clog 2 v
  have hv' : 1 < v := by omega
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hv'
  have hpos : 0 < n := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by simpa using hv')
  have he : n - 1 + 1 = n := by omega
  refine ⟨n, Nat.le_pow_clog (by decide) v, ?_⟩
  calc
    2 ^ n = 2 ^ (n - 1 + 1) := by rw [he]
    _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
    _ ≤ 2 * v := by change 2 ^ (n - 1) < v at hp; omega

end ESVerify
