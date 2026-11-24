import ESVerify.Coordinates
import ESVerify.Iteration

/-! From the estimates for sets with distinct abscissae to the planar bound. -/

set_option autoImplicit false

noncomputable section

namespace ESVerify

/-- The final loss estimate for plane sets, with the small-rank case treated
directly from the rank encoding. -/
theorem planarCubeRootBound
    (hdensity : ∀ X : Finset Point, GeneralPosition X → DistinctAbscissae X →
      X.Nonempty → logCard X ≤ v X)
    (c : ℝ) (hc : 0 ≤ c)
    (hthin : ∀ P : Finset Point, GeneralPosition P → DistinctAbscissae P →
      2 ^ 21 ≤ v P → ThinningStep (fun X => v X) (fun X => h X) P (v P)
        (cubeRootReserve (v P)) c (Real.logb 2 ((v P : ℝ) + 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point, P.Nonempty → GeneralPosition P →
      Real.logb 2 P.card ≤ h P + C * (h P : ℝ) ^ (1 / 3 : ℝ) := by
  let K := 16384 + c *
    (20 + (1 / Real.log 2) * (4 / Real.log 2 + 1 / Real.log (8 / 7)) * 108)
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₈ : 0 < Real.log (8 / 7) := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by unfold K; positivity
  refine ⟨2 ^ 21 + K * (2 : ℝ) ^ (1 / 3 : ℝ), by positivity, ?_⟩
  intro P hP hgp
  obtain ⟨Q, hqg, hqx, hcard, hh⟩ := distinctAbscissae_reduction hgp
  have hQ : Q.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hP.card_pos)
  have hheight : (1 : ℝ) ≤ h Q := by exact_mod_cast one_le_h hQ
  rw [← hcard, ← hh]
  change logCard Q ≤ _
  by_cases hV : 2 ^ 21 ≤ v Q
  · have hm : ∀ X ⊆ Q, X.Nonempty → logCard X ≤ (v X : ℝ) ∧ (v X : ℝ) ≤ v Q := by
      intro X hXQ hX
      exact ⟨hdensity X (fun p hp q hq r hr => hqg p (hXQ hp) q (hXQ hq) r (hXQ hr))
        (fun _ hp _ hq => hqx (hXQ hp) (hXQ hq)) hX, by exact_mod_cast v_mono hXQ⟩
    have hV' : (1 : ℝ) ≤ v Q := by
      exact_mod_cast (show 1 ≤ v Q by omega)
    have hb := cubeRootFromThinning hQ (fun X => (v X : ℝ)) (fun X => (h X : ℝ))
      hV' hc (fun X hX => by exact_mod_cast h_mono hX) hm (hthin Q hqg hqx hV)
    have hvh : (v Q : ℝ) ≤ 2 * h Q := by
      exact_mod_cast (show v Q ≤ 2 * h Q by have := v_add_two_le_two_mul_h hQ; omega)
    have hpow : (v Q : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) *
        (h Q : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) hvh (by norm_num)
    have hm' := mul_le_mul_of_nonneg_left hpow hK
    change logCard Q ≤ (h Q : ℝ) + K * (v Q : ℝ) ^ (1 / 3 : ℝ) at hb
    have hpos : 0 ≤ (2 : ℝ) ^ (21 : ℕ) * (h Q : ℝ) ^ (1 / 3 : ℝ) := by positivity
    linarith
  · have hpow : 1 ≤ (h Q : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hheight (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (2 : ℝ) ^ (21 : ℕ) by positivity)
    have hsmall : (v Q : ℝ) ≤ 2 ^ (21 : ℕ) := by
      exact_mod_cast (le_of_lt (lt_of_not_ge hV))
    have hpos : 0 ≤ K * (2 : ℝ) ^ (1 / 3 : ℝ) * (h Q : ℝ) ^ (1 / 3 : ℝ) := by positivity
    linarith [hdensity Q hqg hqx hQ]

end ESVerify
