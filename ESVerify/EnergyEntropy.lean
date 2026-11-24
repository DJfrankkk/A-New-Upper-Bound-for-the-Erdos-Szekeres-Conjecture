import ESVerify.EnergyApproximation
import ESVerify.EntropyCode
import ESVerify.EntropySupport
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases

/-! An elementary discrete proof of the entropy estimate used in §6. -/

open scoped BigOperators

namespace ESVerify

private def dyadicLength (n : ℕ) : ℕ := 2^n

private theorem dyadicLength_pos (n : ℕ) : 0 < dyadicLength n := by
  unfold dyadicLength
  positivity

private theorem dyadicLength_succ (n : ℕ) : dyadicLength (n+1) = dyadicLength n + dyadicLength n := by
  unfold dyadicLength
  rw [pow_succ]
  omega

private noncomputable def intervalRisk {v : ℕ} (a : Fin v → ℝ) (δ : ℝ) (s n : ℕ) : ℝ :=
  (dyadicLength n : ℝ) * (energy a (s + dyadicLength n) - energy a s) / δ^2

private theorem risk_nonneg {v : ℕ} (a : Fin v → ℝ) (δ : ℝ) (s n : ℕ) :
    0 ≤ intervalRisk a δ s n := by
  unfold intervalRisk
  have hp := sub_nonneg.mpr (energy_mono a (by omega : s ≤ s + dyadicLength n))
  positivity

private theorem risk_split {v : ℕ} (a : Fin v → ℝ) (δ : ℝ) (s n : ℕ) :
    intervalRisk a δ s n + intervalRisk a δ (s + dyadicLength n) n =
      intervalRisk a δ s (n+1) / 2 := by
  unfold intervalRisk
  rw [dyadicLength_succ]
  push_cast
  rw [← Nat.add_assoc]
  ring

private noncomputable def roundHeight {v : ℕ} (a : Fin v → ℝ) (δ : ℝ) (s : ℕ) : ℤ :=
  ⌊pathHeight a s / δ⌋

private noncomputable def adaptiveTree {v : ℕ} (a : Fin v → ℝ) (δ : ℝ) (s : ℕ) :
    ℕ → EntropyTree
  | 0 => .leaf (roundHeight a δ (s+1) - roundHeight a δ s)
  | n+1 => if 1 < intervalRisk a δ s (n+1) then
      .branch (adaptiveTree a δ s n) (adaptiveTree a δ (s + dyadicLength n) n)
    else .leaf (roundHeight a δ (s+dyadicLength (n+1)) - roundHeight a δ s)

private noncomputable def leafBudget (r : ℝ) : ℝ := if r ≤ 1 then 1 else 4 * Real.sqrt r - 1

private theorem leafBudget_ge_one (r : ℝ) : 1 ≤ leafBudget r := by
  by_cases hr : r ≤ 1
  · simp [leafBudget, hr]
  · simp only [leafBudget, if_neg hr]
    have h := Real.sqrt_le_sqrt (le_of_not_ge hr)
    rw [Real.sqrt_one] at h
    linarith

private theorem leafBudget_split {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 1 < r) (hrpq : p + q = r / 2) : leafBudget p + leafBudget q ≤ leafBudget r := by
  have hr₀ : 0 ≤ r := by linarith
  have hroot := Real.sq_sqrt hr₀
  have hpr := Real.sq_sqrt hp
  have hqr := Real.sq_sqrt hq
  have hr₁ : 1 ≤ Real.sqrt r := by simpa using Real.sqrt_le_sqrt hr.le
  have hroot_nonneg := Real.sqrt_nonneg r
  have hp_nonneg := Real.sqrt_nonneg p
  have hq_nonneg := Real.sqrt_nonneg q
  have hmain : Real.sqrt p + Real.sqrt q ≤ Real.sqrt r := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) hroot_nonneg
    nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt q)]
  have hsingle (u : ℝ) (hu : 1 < u) (hur : 2*u ≤ r) : 4 * Real.sqrt u ≤ 4 * Real.sqrt r - 1 := by
    have hu₁ : 1 ≤ Real.sqrt u := by simpa using Real.sqrt_le_sqrt hu.le
    have hs : (5/4 : ℝ) * Real.sqrt u ≤ Real.sqrt r := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by decide) hroot_nonneg
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ u)]
    linarith
  by_cases hp₁ : p ≤ 1 <;> by_cases hq₁ : q ≤ 1
  · simp only [leafBudget, if_pos hp₁, if_pos hq₁, if_neg hr.not_ge]
    linarith
  · simp only [leafBudget, if_pos hp₁, if_neg hq₁, if_neg hr.not_ge]
    linarith [hsingle q (lt_of_not_ge hq₁) (by linarith)]
  · simp only [leafBudget, if_neg hp₁, if_pos hq₁, if_neg hr.not_ge]
    linarith [hsingle p (lt_of_not_ge hp₁) (by linarith)]
  · simp only [leafBudget, if_neg hp₁, if_neg hq₁, if_neg hr.not_ge]
    linarith

private theorem adaptiveTree_leaves {v : ℕ} (a : Fin v → ℝ) (δ : ℝ) (s n : ℕ) :
    ((adaptiveTree a δ s n).leaves : ℝ) ≤ leafBudget (intervalRisk a δ s n) := by
  induction n generalizing s with
  | zero => simpa [adaptiveTree, EntropyTree.leaves] using leafBudget_ge_one (intervalRisk a δ s 0)
  | succ n ih =>
    by_cases h : 1 < intervalRisk a δ s (n+1)
    · simp only [adaptiveTree, if_pos h, EntropyTree.leaves, Nat.cast_add]
      apply le_trans (add_le_add (ih s) (ih (s+dyadicLength n)))
      exact leafBudget_split (risk_nonneg a δ s n) (risk_nonneg a δ (s+dyadicLength n) n)
        h (risk_split a δ s n)
    · simpa only [adaptiveTree, if_neg h, EntropyTree.leaves, Nat.cast_one] using
        leafBudget_ge_one (intervalRisk a δ s (n+1))

private theorem heightDiff_le_variation {v : ℕ} (a : Fin v → ℝ) {s t : ℕ} (hst : s ≤ t) :
    |pathHeight a t - pathHeight a s| ≤ variation a t - variation a s := by
  rw [prefix_sub a hst]
  unfold variation
  rw [← Finset.sum_Ico_eq_sub _ hst]
  exact Finset.abs_sum_le_sum_abs _ _

private theorem rounding_error {v : ℕ} (a : Fin v → ℝ) {δ : ℝ} (hd : 0 < δ) (k : ℕ) :
    0 ≤ pathHeight a k - δ * (roundHeight a δ k : ℝ) ∧
      pathHeight a k - δ * (roundHeight a δ k : ℝ) < δ := by
  have hl := Int.floor_le (pathHeight a k / δ)
  have hu := Int.lt_floor_add_one (pathHeight a k / δ)
  change ((roundHeight a δ k : ℤ) : ℝ) ≤ _ at hl
  change _ < ((roundHeight a δ k : ℤ) : ℝ) + 1 at hu
  have hl' := (le_div_iff₀ hd).1 hl
  have hu' := (div_lt_iff₀ hd).1 hu
  constructor <;> linarith

private theorem rounding_jump {v : ℕ} (a : Fin v → ℝ) {δ : ℝ} (hd : 0 < δ)
    {s t : ℕ} (hst : s ≤ t) :
    δ * ((roundHeight a δ t - roundHeight a δ s).natAbs : ℝ) ≤ variation a t - variation a s + δ := by
  have habs (z : ℤ) : δ * (z.natAbs : ℝ) = |δ * (z : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hd.le, ← Int.cast_abs, ← Int.natCast_natAbs]
    simp
  rw [habs, Int.cast_sub, mul_sub]
  have h := heightDiff_le_variation a hst
  have hl := rounding_error a hd s
  have hu := rounding_error a hd t
  rw [abs_le] at h ⊢
  constructor <;> linarith

private theorem adaptiveTree_mass {v : ℕ} (a : Fin v → ℝ) {δ : ℝ} (hd : 0 < δ) (s n : ℕ) :
    δ * ((adaptiveTree a δ s n).jumpMass : ℝ) ≤
      variation a (s+dyadicLength n) - variation a s + δ * ((adaptiveTree a δ s n).leaves : ℝ) := by
  induction n generalizing s with
  | zero =>
    simpa [adaptiveTree, dyadicLength, EntropyTree.leaves, EntropyTree.jumpMass] using
      (rounding_jump a hd (show s ≤ s+1 by omega))
  | succ n ih =>
    by_cases h : 1 < intervalRisk a δ s (n+1)
    · simp only [adaptiveTree, if_pos h, EntropyTree.leaves, EntropyTree.jumpMass, Nat.cast_add,
        dyadicLength_succ, ← Nat.add_assoc]
      linarith [ih s, ih (s+dyadicLength n)]
    · simp only [adaptiveTree, if_neg h, EntropyTree.leaves, EntropyTree.jumpMass, Nat.cast_one, mul_one]
      exact rounding_jump a hd (by omega)

private def treeShift : EntropyTree → ℤ
  | .leaf z => z
  | .branch l r => treeShift l + treeShift r

private def treeHeight : EntropyTree → ℕ → ℕ → ℤ
  | .leaf z, n, k => if k < dyadicLength n then 0 else z
  | .branch l r, n, k =>
      if k < dyadicLength (n-1) then treeHeight l (n-1) k
      else treeShift l + treeHeight r (n-1) (k-dyadicLength (n-1))

private theorem treeHeight_zero (t : EntropyTree) (n : ℕ) : treeHeight t n 0 = 0 := by
  induction t generalizing n with
  | leaf z => simp [treeHeight, dyadicLength_pos]
  | branch l r hl hr => simp [treeHeight, dyadicLength_pos, hl]

private theorem adaptiveTree_shift {v : ℕ} (a : Fin v → ℝ) (δ : ℝ) (s n : ℕ) :
    treeShift (adaptiveTree a δ s n) = roundHeight a δ (s+dyadicLength n) - roundHeight a δ s := by
  induction n generalizing s with
  | zero => simp [adaptiveTree, treeShift, dyadicLength]
  | succ n ih =>
    by_cases h : 1 < intervalRisk a δ s (n+1)
    · simp only [adaptiveTree, if_pos h, treeShift, ih, dyadicLength_succ, ← Nat.add_assoc]
      ring
    · simp [adaptiveTree, if_neg h, treeShift]

private theorem lowRisk_height {v : ℕ} (a : Fin v → ℝ) {δ : ℝ} (hd : 0 < δ)
    {s n k : ℕ} (hk : k ≤ dyadicLength n) (hr : intervalRisk a δ s n ≤ 1) :
    |pathHeight a (s+k) - pathHeight a s| ≤ δ := by
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) hd.le
  have hs := prefix_diff_sq_le a (show s ≤ s+k by omega)
  have hv₀ := sub_nonneg.mpr (energy_mono a (show s ≤ s+k by omega))
  have hS : (k : ℝ) ≤ dyadicLength n := by exact_mod_cast hk
  have hv : energy a (s+k) - energy a s ≤ energy a (s+dyadicLength n) - energy a s := by
    exact sub_le_sub_right (energy_mono a (Nat.add_le_add_left hk s)) _
  rw [Nat.add_sub_cancel_left] at hs
  apply hs.trans
  apply (mul_le_mul hS hv hv₀ (by positivity)).trans
  unfold intervalRisk at hr
  exact (div_le_iff₀ (sq_pos_of_pos hd)).1 hr |>.trans_eq (one_mul _)

private theorem adaptiveTree_eval {v : ℕ} (a : Fin v → ℝ) {δ : ℝ} (hd : 0 < δ) (s n : ℕ) :
    ∀ k ≤ dyadicLength n,
      |pathHeight a (s+k) - δ * ((roundHeight a δ s + treeHeight (adaptiveTree a δ s n) n k : ℤ) : ℝ)| ≤
        2*δ := by
  induction n generalizing s with
  | zero =>
    intro k hk
    change k ≤ 1 at hk
    interval_cases k
    · simp only [adaptiveTree, treeHeight, dyadicLength, pow_zero, Nat.zero_lt_one, if_true,
        add_zero]
      exact (abs_of_nonneg (rounding_error a hd s).1).trans_le (by linarith [(rounding_error a hd s).2])
    · simp only [adaptiveTree, treeHeight, dyadicLength, pow_zero, lt_self_iff_false, if_false,
        add_sub_cancel]
      exact (abs_of_nonneg (rounding_error a hd (s+1)).1).trans_le (by linarith [(rounding_error a hd (s+1)).2])
  | succ n ih =>
    intro k hk
    by_cases h : 1 < intervalRisk a δ s (n+1)
    · by_cases hleft : k < dyadicLength n
      · simpa only [adaptiveTree, if_pos h, treeHeight, Nat.add_sub_cancel, if_pos hleft] using
          ih s k hleft.le
      · have heq : s + dyadicLength n + (k - dyadicLength n) = s+k := by omega
        have ht : roundHeight a δ s + (treeShift (adaptiveTree a δ s n) +
            treeHeight (adaptiveTree a δ (s+dyadicLength n) n) n (k-dyadicLength n)) =
            roundHeight a δ (s+dyadicLength n) +
              treeHeight (adaptiveTree a δ (s+dyadicLength n) n) n (k-dyadicLength n) := by
          rw [adaptiveTree_shift]
          ring
        rw [dyadicLength_succ] at hk
        simpa only [adaptiveTree, if_pos h, treeHeight, Nat.add_sub_cancel, if_neg hleft, ht, heq] using
          ih (s+dyadicLength n) (k-dyadicLength n) (by omega)
    · by_cases hlt : k < dyadicLength (n+1)
      · simp only [adaptiveTree, if_neg h, treeHeight, if_pos hlt, add_zero]
        have hlocal := lowRisk_height a hd hk (le_of_not_gt h)
        have herr := rounding_error a hd s
        rw [abs_le] at hlocal ⊢
        constructor <;> linarith
      · have heq : k = dyadicLength (n+1) := by omega
        subst k
        simp only [adaptiveTree, if_neg h, treeHeight, lt_self_iff_false, if_false, add_sub_cancel]
        have herr := rounding_error a hd (s+dyadicLength (n+1))
        rw [abs_of_nonneg herr.1]
        linarith

/-- A direct entropy bound for anchored sign-path approximants. The constant is
uniform in the dimension, energy, and approximation radius. -/
theorem anchoredEnergyEntropy : AnchoredEnergyEntropy 200 := by
  intro v E d hE hd
  by_cases hv : v = 0
  · subst v
    refine ⟨1, fun _ _ => 0, by norm_num, ?_, ?_⟩
    · simp only [Nat.cast_one, Real.logb_one, Nat.cast_zero, zero_mul, Real.sqrt_zero,
        zero_div, add_zero, mul_one]
      norm_num
    · intro a ha
      refine ⟨0, ?_⟩
      intro k hk
      have : k = 0 := by omega
      subst k
      simpa [pathHeight] using hd.le
  have hv' : 0 < v := Nat.pos_of_ne_zero hv
  obtain ⟨n, hn, hn'⟩ := exists_dyadicLength hv'
  change v ≤ dyadicLength n at hn
  change dyadicLength n ≤ 2*v at hn'
  let δ := d/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let R := Real.sqrt ((v:ℝ)*E) / d
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let L := ⌈4 + 66*R⌉₊
  obtain ⟨M, trees, hM, htrees⟩ := entropyTreeCover L
  let H (m : Fin M) (k : ℕ) : ℝ := δ * (treeHeight (trees m) n k : ℝ)
  refine ⟨M, fun m i => H m (i.val+1) - H m i.val, ?_, ?_, ?_⟩
  · rw [hM]
    positivity
  · have hthree : Real.logb 2 6 ≤ 3 := by
      calc
        _ ≤ Real.logb 2 ((2:ℝ)^3) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
        _ = 3 := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
          norm_num
    have hL : (L : ℝ) < 4 + 66*R + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [hM, Nat.cast_pow, Real.logb_pow]
    norm_num only [Nat.cast_ofNat]
    change (L:ℝ) * Real.logb 2 6 ≤ 200 * (1+R)
    have hmul := mul_le_mul_of_nonneg_left hthree (show (0:ℝ) ≤ L by positivity)
    linarith
  · intro a ha
    let tree := adaptiveTree a δ 0 n
    have hbudget : 3*tree.leaves + tree.jumpMass ≤ L := by
      have hvE : 0 ≤ (v : ℝ)*E := by positivity
      have hroot : (Real.sqrt ((v:ℝ)*E))^2 = (v:ℝ)*E := Real.sq_sqrt hvE
      have hrr : intervalRisk a δ 0 n ≤ 2 * (Real.sqrt ((v:ℝ)*E)/δ)^2 := by
        rw [intervalRisk, zero_add, energy_eq_of_le a hn]
        have hz : energy a 0 = 0 := by simp [energy]
        rw [hz, sub_zero]
        have heq : 2 * (Real.sqrt ((v:ℝ)*E)/δ)^2 = 2 * ((v:ℝ)*E) / δ^2 := by
          rw [div_pow, hroot]
          ring
        rw [heq]
        have hNR : (dyadicLength n : ℝ) ≤ 2 * v := by exact_mod_cast hn'
        exact div_le_div_of_nonneg_right
          ((mul_le_mul hNR ha (energy_nonneg a _) (by positivity)).trans_eq (by ring)) (sq_nonneg δ)
      have hsR : Real.sqrt (intervalRisk a δ 0 n) ≤ 4*R := by
        apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
        have h := Real.sq_sqrt (risk_nonneg a δ 0 n)
        rw [h]
        have hp : 0 ≤ Real.sqrt ((v:ℝ)*E)/δ := by positivity
        calc
          _ ≤ 2*(Real.sqrt ((v:ℝ)*E)/δ)^2 := hrr
          _ = 8*R^2 := by dsimp [δ, R]; ring
          _ ≤ _ := by nlinarith [sq_nonneg R]
      have htree : (tree.leaves : ℝ) ≤ 1 + 16*R := by
        apply (adaptiveTree_leaves a δ 0 n).trans
        unfold leafBudget
        split <;> linarith
      have hvar : variation a (dyadicLength n) ≤ Real.sqrt ((v:ℝ)*energy a v) := variation_bound a hn
      have hvarE : variation a (dyadicLength n) ≤ Real.sqrt ((v:ℝ)*E) :=
        hvar.trans (Real.sqrt_le_sqrt (by gcongr))
      have hmass := adaptiveTree_mass a hδ 0 n
      have hz : variation a 0 = 0 := by simp [variation]
      rw [zero_add, hz, sub_zero] at hmass
      change δ * (tree.jumpMass : ℝ) ≤ _ at hmass
      have hmul : δ * (2*R) = Real.sqrt ((v:ℝ)*E) := by
        dsimp [δ, R]
        field_simp
      have hmass' : (tree.jumpMass : ℝ) ≤ 2*R + tree.leaves := by
        apply (mul_le_mul_iff_of_pos_left hδ).1
        rw [mul_add, hmul]
        linarith
      have hL : 4 + 66*R ≤ (L:ℝ) := Nat.le_ceil _
      exact_mod_cast (show 3 * (tree.leaves:ℝ) + tree.jumpMass ≤ (L:ℝ) by linarith)
    obtain ⟨m, hm⟩ := htrees tree hbudget
    refine ⟨m, ?_⟩
    intro k hk
    rw [pathHeight_differences (H m) hk]
    have hH₀ : H m 0 = 0 := by simp [H, treeHeight_zero]
    rw [hH₀, sub_zero]
    have h := adaptiveTree_eval a hδ 0 n k (hk.trans hn)
    have hr : roundHeight a δ 0 = 0 := by simp [roundHeight, pathHeight]
    simpa [H, hm, tree, hr, show 2*δ = d by dsimp [δ]; ring] using h

end ESVerify
