import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.WLOG

/-! Discrete energies of sign paths and the common approximation of §6. -/

open scoped BigOperators

namespace ESVerify

abbrev SignWord (v : ℕ) := Fin v → Bool

/-- The increments of a word, with `true` representing the positive sign. -/
def signVec {v : ℕ} (w : SignWord v) (i : Fin v) : ℝ := if w i then 1 else -1

def atIndex {v : ℕ} {R : Type*} [Zero R] (a : Fin v → R) (i : ℕ) : R :=
  if h : i < v then a ⟨i, h⟩ else 0

@[simp] theorem atIndex_of_lt {v : ℕ} {R : Type*} [Zero R] (a : Fin v → R)
    {i : ℕ} (hi : i < v) : atIndex a i = a ⟨i, hi⟩ := by simp [atIndex, hi]

/-- Height at an integer time. The walk is constant past its last step. -/
def pathHeight {v : ℕ} (a : Fin v → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, atIndex a i

/-- Energy through an integer time, exactly the integral of the squared slopes
of the linear interpolation on unit intervals. -/
def energy {v : ℕ} (a : Fin v → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (atIndex a i) ^ 2

/-- The corresponding integer-valued height, for counting possible marked heights. -/
def signHeight {v : ℕ} (w : SignWord v) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, atIndex (fun j : Fin v => if w j then (1 : ℤ) else -1) i

theorem signHeight_cast {v : ℕ} (w : SignWord v) (k : ℕ) :
    (signHeight w k : ℝ) = pathHeight (signVec w) k := by
  unfold signHeight pathHeight
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  unfold atIndex signVec
  split
  · split <;> simp_all
  · norm_num

theorem prefix_sub {v : ℕ} (a : Fin v → ℝ) {i j : ℕ} (h : i ≤ j) :
    pathHeight a j - pathHeight a i = ∑ k ∈ Finset.Ico i j, atIndex a k := by
  symm
  exact Finset.sum_Ico_eq_sub _ h

theorem energy_sub {v : ℕ} (a : Fin v → ℝ) {i j : ℕ} (h : i ≤ j) :
    energy a j - energy a i = ∑ k ∈ Finset.Ico i j, (atIndex a k) ^ 2 := by
  symm
  exact Finset.sum_Ico_eq_sub _ h

theorem energy_nonneg {v : ℕ} (a : Fin v → ℝ) (k : ℕ) : 0 ≤ energy a k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energy_mono {v : ℕ} (a : Fin v → ℝ) : Monotone (energy a) := by
  intro i j h
  apply sub_nonneg.mp
  rw [energy_sub a h]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem prefix_diff_sq_le {v : ℕ} (a : Fin v → ℝ) {i j : ℕ} (h : i ≤ j) :
    |pathHeight a j - pathHeight a i| ^ 2 ≤ ((j - i : ℕ) : ℝ) * (energy a j - energy a i) := by
  rw [prefix_sub a h, energy_sub a h, sq_abs]
  simpa [Nat.card_Ico] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico i j) (fun _ => (1 : ℝ)) (atIndex a))

private theorem signVec_atIndex_abs_le_one {v : ℕ} (w : SignWord v) (i : ℕ) :
    |atIndex (signVec w) i| ≤ 1 := by
  unfold atIndex signVec
  split
  · split <;> norm_num
  · norm_num

theorem signPrefix_lipschitz {v : ℕ} (w : SignWord v) (i j : ℕ) :
    |pathHeight (signVec w) j - pathHeight (signVec w) i| ≤ |(j : ℝ) - i| := by
  wlog h : i ≤ j generalizing i j
  · simpa only [abs_sub_comm] using this j i (le_of_not_ge h)
  rw [prefix_sub (signVec w) h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h)),
    ← Nat.cast_sub h]
  calc
    |∑ k ∈ Finset.Ico i j, atIndex (signVec w) k| ≤
        ∑ k ∈ Finset.Ico i j, |atIndex (signVec w) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Ico i j, (1 : ℝ) :=
      Finset.sum_le_sum fun k _ => signVec_atIndex_abs_le_one w k
    _ = ((j - i : ℕ) : ℝ) := by simp [Nat.card_Ico]

private theorem pathHeight_sub_vec {v : ℕ} (a b : Fin v → ℝ) (k : ℕ) :
    pathHeight (a - b) k = pathHeight a k - pathHeight b k := by
  simp only [pathHeight, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold atIndex
  split <;> simp

private theorem pathHeight_combo {v : ℕ} (u t : ℝ) (a b : Fin v → ℝ) (k : ℕ) :
    pathHeight (u • a + t • b) k = u * pathHeight a k + t * pathHeight b k := by
  simp only [pathHeight, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold atIndex
  split <;> simp

private theorem energy_full {v : ℕ} (a : Fin v → ℝ) : energy a v = ∑ i, a i ^ 2 := by
  rw [Finset.sum_fin_eq_sum_range]
  unfold energy
  apply Finset.sum_congr rfl
  intro i _
  unfold atIndex
  split <;> simp

/-- The total probability of a subset under the uniform sign-word distribution. -/
noncomputable def cubeMeasure {v : ℕ} (A : Finset (SignWord v)) : ℝ := A.card / (2 : ℝ)^v

private theorem cubeMeasure_pos {v : ℕ} {A : Finset (SignWord v)} (hA : A.Nonempty) :
    0 < cubeMeasure A := by
  unfold cubeMeasure
  positivity

/-- The sign words whose heights all lie in the width-`d` strip. -/
noncomputable def stripWords (v d : ℕ) : Finset (SignWord v) := by
  classical
  exact Finset.univ.filter fun w => ∀ k : ℕ, k ≤ v → |pathHeight (signVec w) k| ≤ d

/-- A sign word viewed as a vertex of the Euclidean cube. -/
noncomputable def toCubePoint {v : ℕ} (w : SignWord v) : EuclideanSpace ℝ (Fin v) :=
  (EuclideanSpace.equiv (Fin v) ℝ).symm (signVec w)

/-- Euclidean distance of a cube vertex from the convex hull of a set of vertices. -/
noncomputable def cubeHullDistance {v : ℕ} (w : SignWord v) (A : Finset (SignWord v)) : ℝ :=
  Metric.infDist (toCubePoint w) (convexHull ℝ (toCubePoint '' (A : Set (SignWord v))))

/-- Lawler–Limic killed-walk lower bound used in §6.1. -/
def KilledWalkEstimate : Prop :=
  ∀ v d : ℕ, 0 < d → Real.exp (-8 * (v : ℝ) / (d : ℝ)^2) ≤ cubeMeasure (stripWords v d)

/-- The finite cube concentration bound used from Talagrand, Corollary 2. -/
def TalagrandCubeEstimate : Prop :=
  by
    classical
    exact ∀ {v : ℕ} (A : Finset (SignWord v)), A.Nonempty → ∀ r : ℝ, 0 ≤ r →
      cubeMeasure (Finset.univ.filter fun w => r < cubeHullDistance w A) ≤
        Real.exp (-(r^2) / 8) / cubeMeasure A

/-- The entropy consequence of Birman–Solomyak used in §6.1, restricted to anchored
piecewise-linear functions with unit breakpoints and expressed by their increments.
`K` is independent of the number of steps, the energy and the radius. -/
def AnchoredEnergyEntropy (K : ℝ) : Prop :=
  ∀ (v : ℕ) (E d : ℝ), 0 < E → 0 < d →
    ∃ (M : ℕ) (center : Fin M → Fin v → ℝ),
      0 < M ∧ Real.logb 2 M ≤ K * (1 + Real.sqrt ((v : ℝ) * E) / d) ∧
      ∀ (a : Fin v → ℝ), energy a v ≤ E → ∃ m : Fin M,
        ∀ k : ℕ, k ≤ v → |pathHeight a k - pathHeight (center m) k| ≤ d

/-- The value of the energy bound in Lemma 6.1. -/
noncomputable def approximationEnergy {v : ℕ} (Ω : Finset (SignWord v)) (d : ℕ) : ℝ :=
  64 * (v : ℝ) / (d : ℝ)^2 +
    8 * ((v : ℝ) - Real.logb 2 Ω.card + 1) * Real.log 2

private theorem card_le_cube {v : ℕ} (Ω : Finset (SignWord v)) : Ω.card ≤ 2^v := by
  simpa [SignWord, Fintype.card_fun, Fintype.card_bool] using
    (Finset.card_le_univ Ω)

private theorem approximationEnergy_pos {v d : ℕ} (Ω : Finset (SignWord v))
    (hΩ : Ω.Nonempty) : 0 < approximationEnergy Ω d := by
  have hpos : (0 : ℝ) < Ω.card := by exact_mod_cast hΩ.card_pos
  have hcard : (Ω.card : ℝ) ≤ (2 : ℝ)^v := by exact_mod_cast card_le_cube Ω
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hcard
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  unfold approximationEnergy
  have hb : 0 < (v : ℝ) - Real.logb 2 Ω.card + 1 := by linarith
  positivity

private theorem approximationExp {v d : ℕ} (Ω : Finset (SignWord v))
    (hΩ : Ω.Nonempty) :
    Real.exp (-(approximationEnergy Ω d)/8 + 8 * (v : ℝ)/(d : ℝ)^2) =
      (Ω.card : ℝ) / (2 * (2 : ℝ)^v) := by
  have hpos : (0 : ℝ) < Ω.card := by exact_mod_cast hΩ.card_pos
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have heq : -(approximationEnergy Ω d)/8 + 8 * (v : ℝ)/(d : ℝ)^2 =
      Real.log Ω.card - Real.log 2 - (v : ℝ) * Real.log 2 := by
    unfold approximationEnergy Real.logb
    field_simp
    ring
  rw [heq, Real.exp_sub, Real.exp_sub, Real.exp_log hpos, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [div_div]

private theorem smallHullDistanceApprox {v d : ℕ} {A : Finset (SignWord v)}
    (hA : A.Nonempty) (hAs : A ⊆ stripWords v d) (w : SignWord v) {E : ℝ} (hE : 0 ≤ E)
    (hclose : cubeHullDistance w A ≤ Real.sqrt E) :
    ∃ a : Fin v → ℝ, energy a v ≤ E ∧
      ∀ k : ℕ, k ≤ v → |pathHeight (signVec w) k - pathHeight a k| ≤ d := by
  let S : Set (EuclideanSpace ℝ (Fin v)) := toCubePoint '' (A : Set (SignWord v))
  let C := convexHull ℝ S
  let strip : Set (EuclideanSpace ℝ (Fin v)) :=
    {a | ∀ k : ℕ, k ≤ v → |pathHeight a.ofLp k| ≤ d}
  have hs : S ⊆ strip := by
    rintro a ⟨w', hw', rfl⟩
    simpa [strip, stripWords, toCubePoint] using hAs hw'
  have hconvex : Convex ℝ strip := by
    intro a ha b hb u t hu ht hut k hk
    change |pathHeight (u • a.ofLp + t • b.ofLp) k| ≤ (d : ℝ)
    rw [pathHeight_combo]
    calc
      _ ≤ |u * pathHeight a.ofLp k| + |t * pathHeight b.ofLp k| := abs_add_le _ _
      _ ≤ u * d + t * d := by
        rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg ht]
        exact add_le_add (mul_le_mul_of_nonneg_left (ha k hk) hu)
          (mul_le_mul_of_nonneg_left (hb k hk) ht)
      _ = d := by rw [← add_mul, hut, one_mul]
  have hcsub : C ⊆ strip := convexHull_min hs hconvex
  have hCne : C.Nonempty := by
    obtain ⟨w', hw'⟩ := hA
    exact ⟨toCubePoint w', subset_convexHull ℝ S ⟨w', hw', rfl⟩⟩
  have hCcomp : IsCompact C := ((A.finite_toSet).image toCubePoint).isCompact_convexHull ℝ
  obtain ⟨b, hb, hmin⟩ := hCcomp.exists_isMinOn hCne
    (continuous_const.dist continuous_id).continuousOn
  have hdb : dist (toCubePoint w) b ≤ Real.sqrt E := by
    apply le_trans ((Metric.le_infDist hCne).2 fun y hy => hmin hy)
    exact hclose
  refine ⟨signVec w - b.ofLp, ?_, ?_⟩
  · calc
      energy (signVec w - b.ofLp) v = dist (toCubePoint w) b ^ 2 := by
        rw [energy_full, EuclideanSpace.dist_sq_eq]
        simp [toCubePoint, Real.dist_eq, sq_abs]
      _ ≤ (Real.sqrt E)^2 := by gcongr
      _ = E := Real.sq_sqrt hE
  · intro k hk
    rw [pathHeight_sub_vec, sub_sub_cancel]
    exact hcsub hb k hk

/-- Lemma 6.1, with its inputs from the cited random walk, concentration and entropy
results explicit in the statement. The energy and deviation are those of the linear
interpolation, since their discrete definitions take its slopes and vertex heights. -/
theorem energyApproximation (hkilled : KilledWalkEstimate) (hTalagrand : TalagrandCubeEstimate)
    {K : ℝ} (hEntropy : AnchoredEnergyEntropy K) {v d : ℕ} (hd : 0 < d)
    (Ω : Finset (SignWord v)) (hΩ : Ω.Nonempty) :
    ∃ F ⊆ Ω, F.Nonempty ∧ ∃ a : Fin v → ℝ, energy a v ≤ approximationEnergy Ω d ∧
      (∀ w ∈ F, ∀ k : ℕ, k ≤ v → |pathHeight (signVec w) k - pathHeight a k| ≤ 4 * d) ∧
      Real.logb 2 ((Ω.card : ℝ) / F.card) ≤
        (K + 1) * (1 + Real.sqrt ((v : ℝ) * approximationEnergy Ω d) / d) := by
  classical
  let E := approximationEnergy Ω d
  have hE : 0 < E := approximationEnergy_pos Ω hΩ
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hΩ' : (0 : ℝ) < Ω.card := by exact_mod_cast hΩ.card_pos
  let A := stripWords v d
  have hsmall : Real.exp (-8 * (v : ℝ)/(d : ℝ)^2) ≤ cubeMeasure A := hkilled v d hd
  have hAne : A.Nonempty := by
    by_contra h
    have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, cubeMeasure, Finset.card_empty, Nat.cast_zero, zero_div] at hsmall
    exact (Real.exp_pos _).not_ge hsmall
  let bad : Finset (SignWord v) := Finset.univ.filter fun w => Real.sqrt E < cubeHullDistance w A
  have hbad : (bad.card : ℝ) ≤ Ω.card / 2 := by
    have htal := hTalagrand A hAne (Real.sqrt E) (Real.sqrt_nonneg E)
    change cubeMeasure bad ≤ _ at htal
    rw [Real.sq_sqrt hE.le] at htal
    have hr : cubeMeasure bad ≤ (Ω.card : ℝ) / (2 * (2 : ℝ)^v) := calc
      _ ≤ Real.exp (-E/8) / cubeMeasure A := htal
      _ ≤ Real.exp (-E/8) / Real.exp (-8 * (v : ℝ)/(d : ℝ)^2) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hsmall
      _ = (Ω.card : ℝ) / (2 * (2 : ℝ)^v) := by
        rw [← Real.exp_sub]
        convert approximationExp Ω hΩ using 2 <;> ring
    unfold cubeMeasure at hr
    rw [← div_div] at hr
    exact (div_le_div_iff_of_pos_right (by positivity)).1 hr
  let good := Ω \ bad
  have hgoodle : Ω.card ≤ 2 * good.card := by
    have hbadΩ : 2 * (Ω ∩ bad).card ≤ Ω.card := by
      have hh : ((Ω ∩ bad).card : ℝ) ≤ bad.card := by exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      exact_mod_cast (show (2 : ℝ) * (Ω ∩ bad).card ≤ Ω.card by linarith)
    have heq : good = Ω \ (Ω ∩ bad) := by
      ext w
      simp [good]
    rw [heq, Finset.card_sdiff_of_subset Finset.inter_subset_left]
    omega
  have hgoodne : good.Nonempty := by
    rw [← Finset.card_pos]
    have := hΩ.card_pos
    omega
  have hw : ∀ w : good, ∃ a : Fin v → ℝ, energy a v ≤ E ∧
      ∀ k : ℕ, k ≤ v → |pathHeight (signVec w.val) k - pathHeight a k| ≤ d := by
    intro w
    have hh := (Finset.mem_sdiff.mp w.property).2
    apply smallHullDistanceApprox hAne (Finset.Subset.refl A) w.val hE.le
    simpa [bad, not_lt] using hh
  choose a ha using hw
  obtain ⟨M, center, hM, hMlog, hcover⟩ := hEntropy v E d hE hd'
  have hcover' : ∀ w : good, ∃ m : Fin M,
      ∀ k : ℕ, k ≤ v → |pathHeight (a w) k - pathHeight (center m) k| ≤ d :=
    fun w => hcover (a w) (ha w).1
  choose cls hcls using hcover'
  let G := good.attach
  let U : Finset (Fin M) := Finset.univ
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hG' : (0 : ℝ) < good.card := by exact_mod_cast hgoodne.card_pos
  have hUne : U.Nonempty := Finset.card_pos.mp (by simpa [U] using hM)
  have hsize : U.card • ((good.card : ℝ) / M) ≤ (G.card : ℝ) := by
    simp only [U, G, Finset.card_univ, Fintype.card_fin, Finset.card_attach, nsmul_eq_mul]
    field_simp
    rfl
  obtain ⟨m, _, hm⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (f := cls) (fun _ _ => Finset.mem_univ _) hUne hsize
  let f := G.filter fun w => cls w = m
  have hflen : (good.card : ℝ) / M ≤ f.card := hm
  have hfne : f.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast (show (0 : ℝ) < f.card from (div_pos hG' hM').trans_le hflen)
  let e : good ↪ SignWord v := ⟨Subtype.val, Subtype.val_injective⟩
  let F := f.map e
  have hFle : F ⊆ Ω := by
    intro w hw'
    obtain ⟨u, _, hu⟩ := Finset.mem_map.mp hw'
    subst w
    exact (Finset.mem_sdiff.mp u.property).1
  have hFn : F.Nonempty := hfne.map
  obtain ⟨w₀, hw₀⟩ := hfne
  have hw₀m : cls w₀ = m := (Finset.mem_filter.mp hw₀).2
  refine ⟨F, hFle, hFn, a w₀, (ha w₀).1, ?_, ?_⟩
  · intro w hwF k hk
    obtain ⟨u, hu, hu'⟩ := Finset.mem_map.mp hwF
    have hum : cls u = m := (Finset.mem_filter.mp hu).2
    have h₁ := (ha u).2 k hk
    have h₂ := hcls u k hk
    have h₃ := hcls w₀ k hk
    rw [hum] at h₂
    rw [hw₀m] at h₃
    change u.val = w at hu'
    subst w
    apply abs_le.mpr
    obtain ⟨h₁a,h₁b⟩ := abs_le.mp h₁
    obtain ⟨h₂a,h₂b⟩ := abs_le.mp h₂
    obtain ⟨h₃a,h₃b⟩ := abs_le.mp h₃
    constructor <;> linarith
  · have hFpos : (0 : ℝ) < F.card := by exact_mod_cast hFn.card_pos
    have hfsize : (good.card : ℝ) ≤ F.card * M := by
      rw [Finset.card_map]
      exact (div_le_iff₀ hM').1 hflen
    have hsize' : (Ω.card : ℝ) / F.card ≤ 2 * M := by
      apply (div_le_iff₀ hFpos).2
      have hgreal : (Ω.card : ℝ) ≤ 2 * good.card := by exact_mod_cast hgoodle
      nlinarith
    calc
      _ ≤ Real.logb 2 (2 * M) :=
        Real.logb_le_logb_of_le (by norm_num) (div_pos hΩ' hFpos) hsize'
      _ = 1 + Real.logb 2 M := by
        rw [Real.logb_mul (by norm_num) (ne_of_gt hM'), Real.logb_self_eq_one (by norm_num)]
      _ ≤ (K + 1) * (1 + Real.sqrt ((v : ℝ)*E) / d) := by
        have hz : 0 ≤ Real.sqrt ((v : ℝ)*E) / d := by positivity
        linarith

end ESVerify
