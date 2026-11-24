import ESVerify.EnergyApproximation
import Mathlib.Tactic

/-! The geometric step of the cube convex-distance induction. -/

set_option autoImplicit false

namespace ESVerify

open scoped BigOperators

/-- Delete the first coordinate from the words with first sign \(b\). -/
noncomputable def cubeSection {v : ℕ} (A : Finset (SignWord (v + 1))) (b : Bool) :
    Finset (SignWord v) := by
  classical
  exact Finset.univ.filter fun w => Fin.cons b w ∈ A

@[simp] theorem mem_cubeSection {v : ℕ} {A : Finset (SignWord (v + 1))}
    {b : Bool} {w : SignWord v} : w ∈ cubeSection A b ↔ Fin.cons b w ∈ A := by
  classical
  simp [cubeSection]

private def headSign (b : Bool) : ℝ := if b then 1 else -1

private noncomputable def prepend {v : ℕ} (h : ℝ) (x : EuclideanSpace ℝ (Fin v)) :
    EuclideanSpace ℝ (Fin (v + 1)) :=
  (EuclideanSpace.equiv (Fin (v + 1)) ℝ).symm (Fin.cons h x.ofLp)

@[simp] private theorem prepend_zero {v : ℕ} (h : ℝ) (x : EuclideanSpace ℝ (Fin v)) :
    prepend h x 0 = h := by simp [prepend]

@[simp] private theorem prepend_succ {v : ℕ} (h : ℝ) (x : EuclideanSpace ℝ (Fin v))
    (i : Fin v) : prepend h x i.succ = x i := by simp [prepend]

@[simp] private theorem cubePoint_cons_zero {v : ℕ} (b : Bool) (w : SignWord v) :
    toCubePoint (Fin.cons b w) 0 = headSign b := by simp [toCubePoint, signVec, headSign]

@[simp] private theorem cubePoint_cons_succ {v : ℕ} (b : Bool) (w : SignWord v) (i : Fin v) :
    toCubePoint (Fin.cons b w) i.succ = toCubePoint w i := by simp [toCubePoint, signVec]

private theorem prepend_cubePoint {v : ℕ} (b : Bool) (w : SignWord v) :
    prepend (headSign b) (toCubePoint w) = toCubePoint (Fin.cons b w) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem prepend_combo {v : ℕ} (a b h h' : ℝ) (x y : EuclideanSpace ℝ (Fin v)) :
    a • prepend h x + b • prepend h' y =
      prepend (a * h + b * h') (a • x + b • y) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [smul_eq_mul]

private def wordHull {v : ℕ} (A : Finset (SignWord v)) : Set (EuclideanSpace ℝ (Fin v)) :=
  convexHull ℝ (toCubePoint '' (A : Set (SignWord v)))

private theorem prepend_mem_wordHull {v : ℕ} {A : Finset (SignWord (v + 1))}
    {b : Bool} {x : EuclideanSpace ℝ (Fin v)} (hx : x ∈ wordHull (cubeSection A b)) :
    prepend (headSign b) x ∈ wordHull A := by
  let S : Set (EuclideanSpace ℝ (Fin v)) := {z | prepend (headSign b) z ∈ wordHull A}
  have hS : Convex ℝ S := by
    intro x hx y hy a c ha hc hac
    have hcHull : Convex ℝ (wordHull A) := convex_convexHull ℝ _
    have hh := hcHull hx hy ha hc hac
    rw [prepend_combo, ← add_mul, hac, one_mul] at hh
    exact hh
  have hsub : toCubePoint '' (cubeSection A b : Set (SignWord v)) ⊆ S := by
    rintro _ ⟨w, hw, rfl⟩
    change prepend (headSign b) (toCubePoint w) ∈ wordHull A
    rw [prepend_cubePoint]
    exact subset_convexHull ℝ _ ⟨_, mem_cubeSection.mp hw, rfl⟩
  exact convexHull_min hsub hS hx

private theorem exists_hull_minimizer {v : ℕ} {A : Finset (SignWord v)}
    (hA : A.Nonempty) (w : SignWord v) :
    ∃ x ∈ wordHull A, dist (toCubePoint w) x = cubeHullDistance w A := by
  have hne : (wordHull A).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨toCubePoint a, subset_convexHull ℝ _ ⟨a, ha, rfl⟩⟩
  have hcompact : IsCompact (wordHull A) :=
    ((A.finite_toSet).image toCubePoint).isCompact_convexHull ℝ
  obtain ⟨x, hx, hmin⟩ :=
    hcompact.exists_isMinOn hne (continuous_const.dist continuous_id).continuousOn
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · exact (Metric.le_infDist hne).mpr fun y hy => hmin hy
  · exact Metric.infDist_le_dist_of_mem hx

private theorem dist_sq_prepend {v : ℕ} (b : Bool) (w : SignWord v)
    (h : ℝ) (x : EuclideanSpace ℝ (Fin v)) :
    dist (toCubePoint (Fin.cons b w)) (prepend h x) ^ 2 =
      (headSign b - h) ^ 2 + dist (toCubePoint w) x ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_succ]
  simp [Real.dist_eq, sq_abs]

private theorem hullDist_sq_le {v : ℕ} (w : SignWord v) {A : Finset (SignWord v)}
    {x : EuclideanSpace ℝ (Fin v)} (hx : x ∈ wordHull A) :
    cubeHullDistance w A ^ 2 ≤ dist (toCubePoint w) x ^ 2 :=
  pow_le_pow_left₀ Metric.infDist_nonneg (Metric.infDist_le_dist_of_mem hx) _

private theorem tailDist_sq_combo {v : ℕ} (z x y : EuclideanSpace ℝ (Fin v))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    dist z (r • x + (1 - r) • y) ^ 2 ≤
      (1 - r) * dist z y ^ 2 + r * dist z x ^ 2 := by
  simp only [EuclideanSpace.dist_sq_eq, Real.dist_eq, sq_abs, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hr1)) (sq_nonneg (x i - y i))
  nlinarith only [h]

private theorem cubeDistSq_cons_section {v : ℕ} (A : Finset (SignWord (v + 1))) (b c : Bool)
    (w : SignWord v) (hc : (cubeSection A c).Nonempty) :
    cubeHullDistance (Fin.cons b w) A ^ 2 ≤
      cubeHullDistance w (cubeSection A c) ^ 2 + (headSign b - headSign c) ^ 2 := by
  obtain ⟨x, hx, hmin⟩ := exists_hull_minimizer hc w
  calc
    _ ≤ dist (toCubePoint (Fin.cons b w)) (prepend (headSign c) x) ^ 2 :=
      hullDist_sq_le _ (prepend_mem_wordHull hx)
    _ = _ := by rw [dist_sq_prepend, hmin, add_comm]

theorem cubeDistSq_cons_same {v : ℕ} (A : Finset (SignWord (v + 1))) (b : Bool)
    (w : SignWord v) (h : (cubeSection A b).Nonempty) :
    cubeHullDistance (Fin.cons b w) A ^ 2 ≤ cubeHullDistance w (cubeSection A b) ^ 2 := by
  simpa using cubeDistSq_cons_section A b b w h

theorem cubeDistSq_cons_other {v : ℕ} (A : Finset (SignWord (v + 1))) (b : Bool)
    (w : SignWord v) (h : (cubeSection A (!b)).Nonempty) :
    cubeHullDistance (Fin.cons b w) A ^ 2 ≤
      cubeHullDistance w (cubeSection A (!b)) ^ 2 + 4 := by
  have hh : (headSign b - headSign (!b)) ^ 2 = 4 := by cases b <;> norm_num [headSign]
  rw [← hh]
  exact cubeDistSq_cons_section A b (!b) w h

theorem cubeDistSq_cons_mix {v : ℕ} (A : Finset (SignWord (v + 1))) (b : Bool)
    (w : SignWord v) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hsame : (cubeSection A b).Nonempty) (hother : (cubeSection A (!b)).Nonempty) :
    cubeHullDistance (Fin.cons b w) A ^ 2 ≤
      (1 - r) * cubeHullDistance w (cubeSection A (!b)) ^ 2 +
      r * cubeHullDistance w (cubeSection A b) ^ 2 + 4 * (1 - r) ^ 2 := by
  obtain ⟨x, hx, hxMin⟩ := exists_hull_minimizer hsame w
  obtain ⟨y, hy, hyMin⟩ := exists_hull_minimizer hother w
  have hCombo : r • prepend (headSign b) x + (1 - r) • prepend (headSign (!b)) y ∈
      wordHull A := by
    have convexHullA : Convex ℝ (wordHull A) := convex_convexHull ℝ _
    exact convexHullA (prepend_mem_wordHull hx) (prepend_mem_wordHull hy) hr0
      (sub_nonneg.mpr hr1) (by ring)
  have hhead : (headSign b - (r * headSign b + (1 - r) * headSign (!b))) ^ 2 =
      4 * (1 - r) ^ 2 := by
    cases b <;> simp [headSign] <;> ring
  have htail := tailDist_sq_combo (toCubePoint w) x y hr0 hr1
  rw [hxMin, hyMin] at htail
  calc
    _ ≤ dist (toCubePoint (Fin.cons b w))
        (r • prepend (headSign b) x + (1 - r) • prepend (headSign (!b)) y) ^ 2 :=
      hullDist_sq_le _ hCombo
    _ = _ + dist (toCubePoint w) (r • x + (1 - r) • y) ^ 2 := by
      rw [prepend_combo, dist_sq_prepend, hhead]
    _ ≤ _ := by linarith

end ESVerify

