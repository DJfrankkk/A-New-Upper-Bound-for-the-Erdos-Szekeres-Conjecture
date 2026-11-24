import ESVerify.Theorem
import ESVerify.Talagrand
import ESVerify.KilledWalk
import ESVerify.EnergyEntropy
import ESVerify.Equipartition
import ESVerify.PlanarEquipartition
import ESVerify.ErdosSzekeresNumber

/-! Lean verification of Theorem 1.1 and its Erdős–Szekeres number corollary. -/

set_option autoImplicit false

namespace ESVerify

/-- The cube-root bound of Hu, Shao, and Shen. -/
theorem cube_root_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point, P.Nonempty → GeneralPosition P →
      Real.logb 2 P.card ≤ h P + C * (h P : ℝ) ^ (1 / 3 : ℝ) :=
  cube_root_bound_of_estimates killedWalkEstimate talagrandCubeEstimate
    (by norm_num) anchoredEnergyEntropy
    (fun _ hg hx => twoLineEquipartition_of_cuts (@equipartition_cuts) hg hx)

/-- The resulting upper bound on the least Erdős–Szekeres threshold. -/
theorem esNumber_cube_root_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      IsESBound n (esNumber n) ∧
        (esNumber n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + C * (n : ℝ) ^ (1 / 3 : ℝ)) :=
  esNumber_bound_of_log_height cube_root_bound

#print axioms cube_root_bound
#print axioms esNumber_cube_root_bound

end ESVerify
