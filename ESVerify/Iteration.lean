import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! The loss accounting in Section 7 of the Erdős–Szekeres proof. -/

set_option autoImplicit false

namespace ESVerify

/-- The binary logarithm of the number of points. -/
noncomputable def logCard {α : Type*} (X : Finset α) : ℝ :=
  Real.logb 2 X.card

/-- The logarithmic deficit with an additive reserve. -/
noncomputable def slack {α : Type*} (v : Finset α → ℝ) (W : ℝ) (X : Finset α) : ℝ :=
  W + v X - logCard X

/-- The cost of one thinning step. -/
noncomputable def thinningCost (V c L z : ℝ) : ℝ :=
  c * (Real.sqrt (V / z) + L)

private noncomputable def remainingCost (V W c L z : ℝ) : ℝ :=
  c * (16 * (Real.sqrt (V / W) - Real.sqrt (V / z)) +
    L * Real.logb (8 / 7) (z / W))

private theorem remainingCost_nonneg {V W c L z : ℝ}
    (hV : 0 ≤ V) (hW : 0 < W) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hz : W ≤ z) : 0 ≤ remainingCost V W c L z := by
  have hs := Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hV hW hz)
  have hlog : 0 ≤ Real.logb (8 / 7) (z / W) :=
    Real.logb_nonneg (by norm_num) ((le_div_iff₀ hW).2 (by simpa))
  unfold remainingCost
  positivity

private theorem remainingCost_step {V W c L z z' : ℝ}
    (hV : 0 ≤ V) (hW : 0 < W) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hz' : W ≤ z') (hstep : z' < (7 / 8) * z) :
    thinningCost V c L z + remainingCost V W c L z' ≤ remainingCost V W c L z := by
  have hp' : 0 < z' := hW.trans_le hz'
  have hp : 0 < z := by linarith
  have hr : z' ≤ (7 / 8) * z := hstep.le
  have hsum : (17 / 16 : ℝ) * Real.sqrt (V / z) ≤ Real.sqrt (V / z') := by
    have hdiv : V / z ≤ (7 / 8) * (V / z') := by
      apply (div_le_iff₀ hp).2
      calc
        V = (V / z') * z' := by field_simp
        _ ≤ (V / z') * ((7 / 8) * z) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
        _ = (7 / 8) * (V / z') * z := by ring
    have ht : (17 / 16 : ℝ) ^ 2 * (V / z) ≤ V / z' := by
      calc
        _ ≤ (17 / 16 : ℝ) ^ 2 * ((7 / 8) * (V / z')) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ ≤ V / z' := by nlinarith [show 0 ≤ V / z' by positivity]
    calc
      _ = Real.sqrt ((17 / 16 : ℝ) ^ 2 * (V / z)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ ≤ _ := Real.sqrt_le_sqrt ht
  have hdiff : 1 + Real.logb (8 / 7) (z' / W) ≤ Real.logb (8 / 7) (z / W) := by
    have harg : (8 / 7) * (z' / W) ≤ z / W := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hW]
      linarith
    calc
      _ = Real.logb (8 / 7) ((8 / 7) * (z' / W)) := by
        rw [Real.logb_mul (by norm_num) (by positivity), show Real.logb (8 / 7) (8 / 7) = 1 by rw [Real.logb, div_self (Real.log_pos (by norm_num)).ne']]
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by positivity) harg
  have hlog := mul_le_mul_of_nonneg_left hdiff hL
  unfold thinningCost remainingCost
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ hc
  linarith

private theorem remainingCost_le {V W c L z : ℝ}
    (hW : 0 < W) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hz : W ≤ z) (hzV : z ≤ W + V) :
    remainingCost V W c L z ≤
      c * (16 * Real.sqrt (V / W) + L * Real.logb (8 / 7) ((W + V) / W)) := by
  have hlog : Real.logb (8 / 7) (z / W) ≤ Real.logb (8 / 7) ((W + V) / W) :=
    Real.logb_le_logb_of_le (by norm_num) (div_pos (hW.trans_le hz) hW)
      ((div_le_div_iff_of_pos_right hW).2 hzV)
  unfold remainingCost
  apply mul_le_mul_of_nonneg_left _ hc
  linarith [Real.sqrt_nonneg (V / z), mul_le_mul_of_nonneg_left hlog hL]

/-- Each successful thinning pays for its own loss by reducing a potential.
This is the reverse geometric-series argument expressed as a telescoping bound. -/
theorem logarithmicIteration {α : Type*} {P : Finset α} (hP : P.Nonempty)
    (v : Finset α → ℝ) {V W c L target : ℝ}
    (hV : 0 ≤ V) (hW : 0 < W) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hslack : ∀ X ⊆ P, X.Nonempty → W ≤ slack v W X ∧ slack v W X ≤ W + V)
    (hstep : ∀ X ⊆ P, X.Nonempty →
      logCard X ≤ target ∨
      ∃ H ⊂ X, H.Nonempty ∧
        logCard X - logCard H ≤ thinningCost V c L (slack v W X) ∧
        slack v W H < (7 / 8) * slack v W X) :
    logCard P ≤ target +
      c * (16 * Real.sqrt (V / W) + L * Real.logb (8 / 7) ((W + V) / W)) := by
  suffices h : ∀ X ⊆ P, X.Nonempty →
      logCard X ≤ target + remainingCost V W c L (slack v W X) by
    exact (h P (by rfl) hP).trans (add_le_add_right
      (remainingCost_le hW hc hL (hslack P (by rfl) hP).1 (hslack P (by rfl) hP).2) _)
  intro X
  refine Finset.strongInductionOn X ?_
  intro X ih hXP hX
  rcases hstep X hXP hX with hstop | ⟨H, hHX, hH, hloss, hcontract⟩
  · have hp := remainingCost_nonneg hV hW hc hL (hslack X hXP hX).1
    linarith
  · have hHP := hHX.1.trans hXP
    have hrec := ih H hHX hHP hH
    have hpay :=
      remainingCost_step hV hW hc hL (hslack H hHP hH).1 hcontract
    linarith

/-- A point-set implementation of the two alternatives needed in Section 7. -/
def ThinningStep {α : Type*} (v height : Finset α → ℝ) (P : Finset α)
    (V W c L : ℝ) : Prop :=
  ∀ X ⊆ P, X.Nonempty →
    logCard X ≤ height X + W + 4 * thinningCost V c L (slack v W X) ∨
    ∃ H ⊂ X, H.Nonempty ∧
      logCard X - logCard H ≤ thinningCost V c L (slack v W X) ∧
      slack v W H < (7 / 8) * slack v W X

theorem logarithmicBound {α : Type*} {P : Finset α} (hP : P.Nonempty)
    (v height : Finset α → ℝ) {V W c L : ℝ}
    (hV : 0 ≤ V) (hW : 0 < W) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hheight : ∀ X ⊆ P, height X ≤ height P)
    (hrank : ∀ X ⊆ P, X.Nonempty → logCard X ≤ v X ∧ v X ≤ V)
    (hstep : ThinningStep v height P V W c L) :
    logCard P ≤ height P + W + 4 * thinningCost V c L W +
      c * (16 * Real.sqrt (V / W) + L * Real.logb (8 / 7) ((W + V) / W)) := by
  have hslack : ∀ X ⊆ P, X.Nonempty → W ≤ slack v W X ∧ slack v W X ≤ W + V := by
    intro X hXP hX
    obtain ⟨h₁, h₂⟩ := hrank X hXP hX
    have h₃ : 0 ≤ logCard X :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hX.card_pos)
    unfold slack
    exact ⟨by linarith, by linarith⟩
  refine logarithmicIteration hP v hV hW hc hL hslack ?_
  intro X hXP hX
  rcases hstep X hXP hX with h | h
  · left
    have hs := Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hV hW (hslack X hXP hX).1)
    have he : thinningCost V c L (slack v W X) ≤ thinningCost V c L W :=
      mul_le_mul_of_nonneg_left (add_le_add_left hs L) hc
    linarith [hheight X hXP]
  · exact Or.inr h


/-- The reserve used in Proposition 5.1. -/
noncomputable def cubeRootReserve (V : ℝ) : ℝ := 16384 * V ^ (1 / 3 : ℝ)

private theorem naturalLog_sq_le {u : ℝ} (hu : 1 ≤ u) :
    Real.log u ^ 2 ≤ 36 * u ^ (1 / 3 : ℝ) := by
  have hp : 0 < u := zero_lt_one.trans_le hu
  have h₀ := Real.log_nonneg hu
  have h₁ : Real.log u ≤ 6 * u ^ (1 / 6 : ℝ) := by
    have h := Real.add_one_le_exp (Real.log u / 6)
    rw [show Real.log u / 6 = Real.log u * (1 / 6 : ℝ) by ring,
      ← Real.rpow_def_of_pos hp] at h
    linarith
  calc
    _ ≤ (6 * u ^ (1 / 6 : ℝ)) ^ 2 := by gcongr
    _ = 36 * u ^ (1 / 3 : ℝ) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hp.le]
      norm_num

private theorem sqrt_loss_le {V : ℝ} (hV : 1 ≤ V) :
    Real.sqrt (V / cubeRootReserve V) ≤ V ^ (1 / 3 : ℝ) := by
  have hp : 0 < V := zero_lt_one.trans_le hV
  have hr : 0 < V ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hp _
  have hpow : (V ^ (1 / 3 : ℝ)) ^ 3 = V := by
    rw [← Real.rpow_mul_natCast hp.le]
    norm_num
  calc
    _ ≤ Real.sqrt ((V ^ (1 / 3 : ℝ)) ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply (div_le_iff₀ (show 0 < cubeRootReserve V by unfold cubeRootReserve; positivity)).2
      calc
        _ = (V ^ (1 / 3 : ℝ)) ^ 3 := hpow.symm
        _ ≤ (V ^ (1 / 3 : ℝ)) ^ 2 * cubeRootReserve V := by
          unfold cubeRootReserve
          nlinarith [pow_nonneg hr.le 3]
    _ = _ := Real.sqrt_sq hr.le

private theorem log_growth_le {V : ℝ} (hV : 1 ≤ V) :
    Real.log (V + 2) ^ 2 ≤ 108 * V ^ (1 / 3 : ℝ) := by
  have hp : 0 ≤ V := by linarith
  calc
    _ ≤ 36 * (V + 2) ^ (1 / 3 : ℝ) := naturalLog_sq_le (by linarith)
    _ ≤ 36 * (3 * V) ^ (1 / 3 : ℝ) := by gcongr; linarith
    _ = 36 * (3 : ℝ) ^ (1 / 3 : ℝ) * V ^ (1 / 3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hp]
      ring
    _ ≤ _ := by
      have hh : (3 : ℝ) ^ (1 / 3 : ℝ) ≤ 3 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          (by norm_num : (1 / 3 : ℝ) ≤ 1)
      gcongr
      linarith

private theorem log_loss_le {V : ℝ} (hV : 1 ≤ V) :
    4 * Real.logb 2 (V + 2) +
      Real.logb 2 (V + 2) * Real.logb (8 / 7)
        ((cubeRootReserve V + V) / cubeRootReserve V) ≤
      ((1 / Real.log 2) * (4 / Real.log 2 + 1 / Real.log (8 / 7)) * 108) *
        V ^ (1 / 3 : ℝ) := by
  have hW : 1 ≤ cubeRootReserve V := by
    have hh : 1 ≤ V ^ (1 / 3 : ℝ) := Real.one_le_rpow hV (by norm_num)
    unfold cubeRootReserve
    linarith
  have hWp : 0 < cubeRootReserve V := zero_lt_one.trans_le hW
  have hp : 0 < V := zero_lt_one.trans_le hV
  have hh : (cubeRootReserve V + V) / cubeRootReserve V ≤ V + 2 := by
    rw [add_div, div_self hWp.ne']
    linarith [div_le_div_of_nonneg_left hp.le zero_lt_one hW]
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 8 / 7)
    (show 0 < (cubeRootReserve V + V) / cubeRootReserve V by positivity) hh
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₈ : 0 < Real.log (8 / 7) := Real.log_pos (by norm_num)
  have hlog₀ : 0 ≤ Real.log (V + 2) := Real.log_nonneg (by linarith)
  have hlog₁ : Real.log 2 ≤ Real.log (V + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog_loss : 4 * Real.logb 2 (V + 2) ≤
      (4 / Real.log 2 ^ 2) * Real.log (V + 2) ^ 2 := by
    unfold Real.logb
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos h₂ 2)).2
    have hh₂ : Real.log (V + 2) * Real.log 2 ≤ Real.log (V + 2) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlog₁ hlog₀]
    have hid : 4 * (Real.log (V + 2) / Real.log 2) * Real.log 2 ^ 2 =
        4 * (Real.log (V + 2) * Real.log 2) := by field_simp
    rw [hid]
    linarith
  have hprod : Real.logb 2 (V + 2) * Real.logb (8 / 7)
      ((cubeRootReserve V + V) / cubeRootReserve V) ≤
      Real.log (V + 2) ^ 2 / (Real.log 2 * Real.log (8 / 7)) := by
    calc
      _ ≤ Real.logb 2 (V + 2) * Real.logb (8 / 7) (V + 2) :=
        mul_le_mul_of_nonneg_left hlog (Real.logb_nonneg (by norm_num) (by linarith))
      _ = _ := by simp [Real.logb, div_mul_div_comm, pow_two]
  calc
    _ ≤ (4 / Real.log 2 ^ 2) * Real.log (V + 2) ^ 2 +
        Real.log (V + 2) ^ 2 / (Real.log 2 * Real.log (8 / 7)) :=
      add_le_add hlog_loss hprod
    _ = ((1 / Real.log 2) * (4 / Real.log 2 + 1 / Real.log (8 / 7))) *
        Real.log (V + 2) ^ 2 := by
      field_simp
    _ ≤ ((1 / Real.log 2) * (4 / Real.log 2 + 1 / Real.log (8 / 7))) *
        (108 * V ^ (1 / 3 : ℝ)) := mul_le_mul_of_nonneg_left (log_growth_le hV) (by positivity)
    _ = _ := by ring

/-- Section 7 with explicit constants, from the rank and thinning estimates. -/
theorem cubeRootFromThinning {α : Type*} {P : Finset α} (hP : P.Nonempty)
    (v height : Finset α → ℝ) {V c : ℝ}
    (hV : 1 ≤ V) (hc : 0 ≤ c)
    (hheight : ∀ X ⊆ P, height X ≤ height P)
    (hrank : ∀ X ⊆ P, X.Nonempty → logCard X ≤ v X ∧ v X ≤ V)
    (hstep : ThinningStep v height P V (cubeRootReserve V) c (Real.logb 2 (V + 2))) :
    logCard P ≤ height P +
      (16384 + c * (20 + (1 / Real.log 2) * (4 / Real.log 2 + 1 / Real.log (8 / 7)) * 108)) *
        V ^ (1 / 3 : ℝ) := by
  have hp : 0 < V := zero_lt_one.trans_le hV
  have hW : 0 < cubeRootReserve V := by unfold cubeRootReserve; positivity
  have hL : 0 ≤ Real.logb 2 (V + 2) := Real.logb_nonneg (by norm_num) (by linarith)
  have hgeneral := logarithmicBound hP v height hp.le hW hc hL hheight hrank hstep
  have hcomplex : 20 * Real.sqrt (V / cubeRootReserve V) +
      (4 * Real.logb 2 (V + 2) + Real.logb 2 (V + 2) * Real.logb (8 / 7)
        ((cubeRootReserve V + V) / cubeRootReserve V)) ≤
      (20 + (1 / Real.log 2) * (4 / Real.log 2 + 1 / Real.log (8 / 7)) * 108) *
        V ^ (1 / 3 : ℝ) := by
    rw [add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (sqrt_loss_le hV) (by norm_num))
      (log_loss_le hV)
  have hpaid := mul_le_mul_of_nonneg_left hcomplex hc
  unfold thinningCost cubeRootReserve at hgeneral
  unfold cubeRootReserve at hpaid
  linarith

end ESVerify
