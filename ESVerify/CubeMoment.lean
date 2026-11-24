import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Scalar and averaging estimates for Talagrand's binary-cube induction. -/

set_option autoImplicit false

open scoped BigOperators

namespace ESVerify

private theorem log_upper_ratio {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - x⁻¹) / 2 := by
  let f : ℝ → ℝ := fun t => (t - t⁻¹) / 2 - Real.log t
  have hd (t : ℝ) (ht : 1 ≤ t) :
      HasDerivAt f ((1 + t⁻¹ ^ 2) / 2 - t⁻¹) t := by
    have ht₀ : t ≠ 0 := by linarith
    unfold f
    convert (((hasDerivAt_id t).sub ((hasDerivAt_id t).inv ht₀)).div_const 2).sub
      (Real.hasDerivAt_log ht₀) using 1
    all_goals first | rfl | (simp [id_eq]; field_simp; ring)
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (show t ∈ Set.Ici (1 : ℝ) from interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (show t ∈ Set.Ici (1 : ℝ) from interior_subset ht)).deriv]
      nlinarith [sq_nonneg (1 - t⁻¹)]
  have h := hmono (by norm_num : (1 : ℝ) ∈ Set.Ici 1) hx hx
  simpa [f, sub_nonneg] using h

private theorem log_lower_ratio {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  let f : ℝ → ℝ := fun t => Real.log t - 2 * (t - 1) / (t + 1)
  have hd (t : ℝ) (ht : 1 ≤ t) :
      HasDerivAt f ((t - 1)^2 / (t * (t + 1)^2)) t := by
    have ht₀ : t ≠ 0 := by linarith
    have ht₁ : t + 1 ≠ 0 := by linarith
    unfold f
    convert (Real.hasDerivAt_log ht₀).sub
      (((hasDerivAt_id t).sub_const 1).const_mul 2 |>.div
        ((hasDerivAt_id t).add_const 1) ht₁) using 1
    all_goals first | rfl | (simp [id_eq]; field_simp; ring)
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (show t ∈ Set.Ici (1 : ℝ) from interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht₁ : 1 ≤ t := show t ∈ Set.Ici (1 : ℝ) from interior_subset ht
      rw [(hd t ht₁).deriv]
      have ht' : 0 < t := zero_lt_one.trans_le ht₁
      positivity
  have h := hmono (by norm_num : (1 : ℝ) ∈ Set.Ici 1) hx hx
  simpa [f, sub_nonneg] using h

theorem cubeMoment_exp_le_ratio {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    Real.exp (1 - r) ≤ (3 - r) / (1 + r) := by
  have hp : 0 < 1 + r := by linarith
  have hratio : 1 ≤ (3 - r) / (1 + r) := (le_div_iff₀ hp).2 (by linarith)
  refine (Real.le_log_iff_exp_le (by linarith)).mp ?_
  have h := log_lower_ratio hratio
  have heq : 2 * ((3 - r) / (1 + r) - 1) / ((3 - r) / (1 + r) + 1) =
      1 - r := by field_simp; ring
  rwa [heq] at h

theorem cubeMoment_weight_bound {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    Real.exp ((1 - r)^2 / 2) * (r⁻¹) ^ r ≤ (3 - r) / (1 + r) := by
  have h := log_upper_ratio (show 1 ≤ r⁻¹ by
    rw [← one_div]; exact (le_div_iff₀ hr).2 (by linarith))
  rw [inv_inv] at h
  have h' := mul_le_mul_of_nonneg_right h hr.le
  have hid : (r⁻¹ - r) / 2 * r = (1 - r^2) / 2 := by field_simp
  rw [hid] at h'
  rw [Real.rpow_def_of_pos (inv_pos.mpr hr), ← Real.exp_add]
  refine (Real.exp_le_exp.mpr (by linarith)).trans (cubeMoment_exp_le_ratio hr.le hr₁)

noncomputable def cubeAverage {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  (∑ x ∈ s, f x) / s.card

/-- Finite Hölder in the form used in the cube induction, where the two
weights sum to one. -/
theorem cubeMoment_holder {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f g : α → ℝ) (hf : ∀ x ∈ s, 0 < f x) (hg : ∀ x ∈ s, 0 < g x)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    cubeAverage s (fun x => f x ^ (1 - r) * g x ^ r) ≤
      cubeAverage s f ^ (1 - r) * cubeAverage s g ^ r := by
  let F := cubeAverage s f
  let G := cubeAverage s g
  have hs' : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hF : 0 < F := div_pos (Finset.sum_pos hf hs) hs'
  have hG : 0 < G := div_pos (Finset.sum_pos hg hs) hs'
  have hpoint (x : α) (hx : x ∈ s) :
      f x ^ (1 - r) * g x ^ r / (F ^ (1 - r) * G ^ r) ≤
        (1 - r) * (f x / F) + r * (g x / G) := by
    rw [← div_mul_div_comm, ← Real.div_rpow (hf x hx).le hF.le,
      ← Real.div_rpow (hg x hx).le hG.le]
    exact Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hr₁) hr₀
      (div_nonneg (hf x hx).le hF.le) (div_nonneg (hg x hx).le hG.le) (by ring)
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hsum
  have hid₁ : (∑ x ∈ s, f x) / F = s.card := by
    change (∑ x ∈ s, f x) / ((∑ x ∈ s, f x) / s.card) = _
    field_simp [(Finset.sum_pos hf hs).ne', hs'.ne']
  have hid₂ : (∑ x ∈ s, g x) / G = s.card := by
    change (∑ x ∈ s, g x) / ((∑ x ∈ s, g x) / s.card) = _
    field_simp [(Finset.sum_pos hg hs).ne', hs'.ne']
  rw [hid₁, hid₂] at hsum
  change (∑ x ∈ s, f x ^ (1 - r) * g x ^ r) / s.card ≤ F ^ (1 - r) * G ^ r
  apply (div_le_iff₀ hs').2
  rw [mul_comm (F ^ (1 - r) * G ^ r)]
  apply (div_le_iff₀ (show 0 < F ^ (1 - r) * G ^ r by positivity)).1
  linarith

end ESVerify
