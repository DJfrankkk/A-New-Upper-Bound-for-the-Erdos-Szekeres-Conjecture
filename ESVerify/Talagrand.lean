import ESVerify.CubeDistance
import ESVerify.CubeMoment

/-! Talagrand's exponential moment bound for the uniform binary cube. -/

set_option autoImplicit false

open scoped BigOperators

namespace ESVerify

private theorem average_cons {v : ℕ} (f : SignWord (v + 1) → ℝ) (b : Bool) :
    cubeAverage Finset.univ f =
      (cubeAverage Finset.univ (fun w => f (Fin.cons b w)) +
        cubeAverage Finset.univ (fun w => f (Fin.cons (!b) w))) / 2 := by
  classical
  have hs : (∑ w, f w) = ∑ bw : Bool × SignWord v, f (Fin.cons bw.1 bw.2) :=
    ((Fin.consEquiv (fun _ : Fin (v + 1) => Bool)).sum_comp f).symm
  unfold cubeAverage
  simp only [Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat, pow_succ]
  rw [hs, Fintype.sum_prod_type, Fintype.sum_bool]
  cases b <;> simp <;> ring

private theorem measure_average {v : ℕ} (A : Finset (SignWord v)) :
    cubeMeasure A = cubeAverage Finset.univ (fun w => if w ∈ A then (1 : ℝ) else 0) := by
  simp [cubeMeasure, cubeAverage]

private theorem measure_cons {v : ℕ} (A : Finset (SignWord (v + 1))) (b : Bool) :
    cubeMeasure A = (cubeMeasure (cubeSection A b) + cubeMeasure (cubeSection A (!b))) / 2 := by
  simp only [measure_average]
  simpa [cubeSection] using average_cons (fun w => if w ∈ A then (1 : ℝ) else 0) b

private noncomputable def moment {v : ℕ} (A : Finset (SignWord v)) : ℝ :=
  cubeAverage Finset.univ fun w => Real.exp (cubeHullDistance w A ^ 2 / 8)

private theorem average_mono {α : Type*} {s : Finset α} {f g : α → ℝ}
    (h : ∀ x ∈ s, f x ≤ g x) : cubeAverage s f ≤ cubeAverage s g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (by positivity)

private theorem average_mul_left {α : Type*} (s : Finset α) (c : ℝ) (f : α → ℝ) :
    cubeAverage s (fun x => c * f x) = c * cubeAverage s f := by
  rw [cubeAverage, cubeAverage, ← Finset.mul_sum, mul_div_assoc]

private theorem section_nonempty {v : ℕ} {A : Finset (SignWord (v + 1))} {b : Bool}
    (h : 0 < cubeMeasure (cubeSection A b)) : (cubeSection A b).Nonempty := by
  contrapose! h
  simp [cubeMeasure, h]

private theorem measure_pos {v : ℕ} {A : Finset (SignWord v)} (h : A.Nonempty) :
    0 < cubeMeasure A := by unfold cubeMeasure; positivity

private theorem tailMoment {v : ℕ} {A : Finset (SignWord (v + 1))} {b : Bool}
    {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (hA : (cubeSection A b).Nonempty)
    (hB : (cubeSection A (!b)).Nonempty) :
    cubeAverage Finset.univ (fun w => Real.exp (cubeHullDistance (Fin.cons (!b) w) A^2 / 8)) ≤
      Real.exp ((1 - r)^2/2) * (moment (cubeSection A b)^(1-r) *
        moment (cubeSection A (!b))^r) := by
  let U : SignWord v → ℝ := fun w => Real.exp (cubeHullDistance w (cubeSection A b)^2 / 8)
  let T : SignWord v → ℝ := fun w => Real.exp (cubeHullDistance w (cubeSection A (!b))^2 / 8)
  calc
    _ ≤ cubeAverage Finset.univ (fun w => Real.exp ((1 - r)^2/2) *
        (U w ^ (1 - r) * T w ^ r)) := by
      apply average_mono
      intro w _
      dsimp [U, T]
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm := cubeDistSq_cons_mix A (!b) w hr hr'
        hB (by simpa only [Bool.not_not] using hA)
      rw [Bool.not_not] at hm
      linarith
    _ ≤ _ := by
      rw [average_mul_left]
      exact mul_le_mul_of_nonneg_left
        (cubeMoment_holder _ Finset.univ_nonempty U T
          (fun w _ => Real.exp_pos _) (fun w _ => Real.exp_pos _) hr hr')
        (Real.exp_pos _).le

private theorem expMoment {v : ℕ} (A : Finset (SignWord v)) (hA : A.Nonempty) :
    moment A ≤ (cubeMeasure A)⁻¹ := by
  classical
  induction v with
  | zero =>
      obtain ⟨w, hw⟩ := hA
      have he : A = Finset.univ := Finset.eq_univ_of_forall fun u =>
        (Subsingleton.elim w u) ▸ hw
      have hh (u : SignWord 0) : cubeHullDistance u A = 0 := by
        unfold cubeHullDistance
        apply Metric.infDist_zero_of_mem
        apply subset_convexHull ℝ
        exact Set.mem_image_of_mem _ (he ▸ Finset.mem_univ u)
      have hm : moment A = 1 := by simp [moment, cubeAverage, hh]
      rw [hm, he]
      simp [cubeMeasure]
  | succ v ih =>
      obtain ⟨b, hord⟩ : ∃ b : Bool,
          cubeMeasure (cubeSection A (!b)) ≤ cubeMeasure (cubeSection A b) := by
        rcases le_total (cubeMeasure (cubeSection A false))
          (cubeMeasure (cubeSection A true)) with h | h
        · exact ⟨true, h⟩
        · exact ⟨false, h⟩
      let a := cubeMeasure (cubeSection A b)
      let s := cubeMeasure (cubeSection A (!b))
      have hsa : s ≤ a := hord
      have hs₀ : 0 ≤ s := by unfold s cubeMeasure; positivity
      have hm : cubeMeasure A = (a + s) / 2 := measure_cons A b
      have ha : 0 < a := by linarith [measure_pos hA]
      have hAn := section_nonempty (b := b) ha
      have hf :
          cubeAverage Finset.univ (fun w => Real.exp (cubeHullDistance (Fin.cons b w) A^2 / 8))
            ≤ a⁻¹ := by
        apply le_trans _ (ih _ hAn)
        apply average_mono
        intro w _
        exact Real.exp_le_exp.mpr (by linarith [cubeDistSq_cons_same A b w hAn])
      rw [moment, average_cons _ b, hm]
      rcases hs₀.eq_or_lt with hs | hs
      · have hg :
          cubeAverage Finset.univ (fun w => Real.exp (cubeHullDistance (Fin.cons (!b) w) A^2 / 8))
            ≤ Real.exp (1/2) * a⁻¹ := calc
          _ ≤ cubeAverage Finset.univ (fun w => Real.exp (1/2) *
              Real.exp (cubeHullDistance w (cubeSection A b)^2 / 8)) := by
            apply average_mono
            intro w _
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hd := cubeDistSq_cons_other A (!b) w
              (by simpa only [Bool.not_not] using hAn)
            rw [Bool.not_not] at hd
            linarith
          _ ≤ _ := by
            rw [average_mul_left]
            exact mul_le_mul_of_nonneg_left (ih _ hAn) (Real.exp_pos _).le
        have he : Real.exp (1/2) ≤ 3 := calc
          _ ≤ Real.exp (1 - (0 : ℝ)) := Real.exp_le_exp.mpr (by norm_num)
          _ ≤ _ := by simpa using cubeMoment_exp_le_ratio (r := 0) (by norm_num) (by norm_num)
        have hmul := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr ha.le)
        have hinv : ((a + s) / 2)⁻¹ = 2 * a⁻¹ := by rw [← hs, add_zero, inv_div, div_eq_mul_inv]
        linarith
      · let r := s / a
        have hr : 0 < r := div_pos hs ha
        have hr' : r ≤ 1 := (div_le_iff₀ ha).2 (by simpa)
        have hBn := section_nonempty (b := !b) hs
        have hid : s⁻¹ = a⁻¹ * r⁻¹ := by
          unfold r
          field_simp
        have hpow : a⁻¹ ^ (1 - r) * s⁻¹ ^ r = a⁻¹ * (r⁻¹) ^ r := by
          rw [hid, Real.mul_rpow (by positivity) (by positivity), ← mul_assoc,
            ← Real.rpow_add (inv_pos.mpr ha), show 1 - r + r = 1 by ring, Real.rpow_one]
        have hF : 0 ≤ moment (cubeSection A b) := by unfold moment cubeAverage; positivity
        have hG : 0 ≤ moment (cubeSection A (!b)) := by unfold moment cubeAverage; positivity
        have hF' := Real.rpow_le_rpow hF (ih _ hAn) (sub_nonneg.mpr hr')
        have hG' := Real.rpow_le_rpow hG (ih _ hBn) hr.le
        change moment (cubeSection A b) ^ (1-r) ≤ a⁻¹ ^ (1-r) at hF'
        change moment (cubeSection A (!b)) ^ r ≤ s⁻¹ ^ r at hG'
        have hg :
            cubeAverage Finset.univ (fun w => Real.exp (cubeHullDistance (Fin.cons (!b) w) A^2 / 8))
              ≤ a⁻¹ * ((3-r)/(1+r)) := calc
          _ ≤ _ := tailMoment hr.le hr' hAn hBn
          _ ≤ Real.exp ((1-r)^2/2) * (a⁻¹ ^ (1-r) * s⁻¹ ^ r) := by
            gcongr
          _ = a⁻¹ * (Real.exp ((1-r)^2/2) * (r⁻¹) ^ r) := by rw [hpow]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (cubeMoment_weight_bound hr hr') (by positivity)
        have hratio : 0 < 1 + r := by linarith
        have hsum : 0 < a + s := by linarith
        have hrId : s = a * r := by unfold r; field_simp
        have hsimpl : (a⁻¹ + a⁻¹ * ((3-r)/(1+r))) / 2 = ((a+s)/2)⁻¹ := by
          rw [inv_div, hrId, show a + a * r = a * (1 + r) by ring]
          field_simp
          ring
        exact (div_le_div_of_nonneg_right (add_le_add hf hg) (by norm_num)).trans_eq hsimpl

theorem talagrandCubeEstimate : TalagrandCubeEstimate := by
  classical
  intro v A hA r hr
  let S := Finset.univ.filter fun w => r < cubeHullDistance w A
  have hp : 0 < Real.exp (r^2/8) := Real.exp_pos _
  have hc : 0 < (2:ℝ)^v := by positivity
  have hs : (S.card : ℝ) * Real.exp (r^2/8) ≤
      ∑ w : SignWord v, Real.exp (cubeHullDistance w A ^ 2 / 8) := calc
    _ = ∑ _w ∈ S, Real.exp (r^2/8) := by simp
    _ ≤ ∑ w ∈ S, Real.exp (cubeHullDistance w A ^ 2 / 8) := by
      apply Finset.sum_le_sum
      intro w hw
      apply Real.exp_le_exp.mpr
      have ht := (Finset.mem_filter.mp hw).2
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr ht.le _) (by norm_num)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => (Real.exp_pos _).le)
  have h := (div_le_div_of_nonneg_right hs hc.le).trans (by
    simpa [moment, cubeAverage, Fintype.card_pi_const] using expMoment A hA)
  change (S.card : ℝ) / (2 : ℝ)^v ≤ Real.exp (-r^2/8) / cubeMeasure A
  calc
    _ ≤ (cubeMeasure A)⁻¹ / Real.exp (r^2/8) :=
      (le_div_iff₀ hp).2 (by rwa [div_mul_eq_mul_div])
    _ = _ := by
      rw [show -r^2/8 = -(r^2/8) by ring, Real.exp_neg]
      ring

end ESVerify
