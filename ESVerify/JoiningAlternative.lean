import ESVerify.ChainPieces
import ESVerify.ConvexChains
import ESVerify.JoiningRanks

set_option autoImplicit false

namespace ESVerify

variable {X T : Finset Point} {V k : ℕ}

/-- The rank-sum difference between the second and first selected groups. -/
def JoiningGroups.rankGap (G : JoiningGroups Prod.fst Prod.snd
    (endingRank X true) (endingRank X false) T V k) : ℝ :=
  (G.x₂ : ℝ) + G.y₂ - ((G.x₁ : ℝ) + G.y₁)

/-- Proposition 4.2 for the joining groups of Proposition 3.2. -/
theorem joiningGroups_alternative (G : JoiningGroups Prod.fst Prod.snd
    (endingRank X true) (endingRank X false) T V k) (hTX : T ⊆ X) (η : ℝ) :
    (v X : ℝ) - G.rankGap - 4 * η + 2 ≤ h X ∨
    ∃ F ∈ ({G.left, G.right} : Set (Finset Point)), ∃ H ⊆ F,
      H.Nonempty ∧ F.card ≤ 2 * H.card ∧ (v H : ℝ) < (v X : ℝ) - η := by
  apply sectionFourAlternative_planar (G.left_subset.trans hTX) (G.right_subset.trans hTX)
    G.left_nonempty G.right_nonempty G.ordered G.left_rank G.right_rank ?_ ?_ ?_ η
  · intro p hp q hq hpq
    simpa only [FirstSide, signed_true, signed_false, neg_lt_neg_iff, slope, joiningSlope]
      using G.left_edges p hp q hq hpq
  · intro p hp q hq hpq
    simpa only [FirstSide, signed_true, signed_false, neg_lt_neg_iff, slope, joiningSlope]
      using G.right_edges p hp q hq hpq
  · exact fun hp hq hpos _ hstart hend => capCup_lengths_add_le_h hp hq hpos hstart hend

/-- Corollary 4.3 for the joining groups of Proposition 3.2. -/
theorem joiningGroups_shrink (G : JoiningGroups Prod.fst Prod.snd
    (endingRank X true) (endingRank X false) T V k) (hTX : T ⊆ X) {W e : ℝ}
    (hW : 0 < W) (he : 0 ≤ e) (hdensity : Real.logb 2 X.card ≤ v X)
    (hgap : G.rankGap ≤ (W + v X - Real.logb 2 X.card) / 2)
    (hsize₁ : 1 + Real.logb 2 X.card - Real.logb 2 G.left.card ≤ e)
    (hsize₂ : 1 + Real.logb 2 X.card - Real.logb 2 G.right.card ≤ e) :
    Real.logb 2 X.card ≤ h X + W + 4 * e ∨
      ∃ H ⊂ X, H.Nonempty ∧ Real.logb 2 X.card - Real.logb 2 H.card ≤ e ∧
        W + v H - Real.logb 2 H.card < (7 / 8 : ℝ) * (W + v X - Real.logb 2 X.card) :=
  sectionFourShrink (v := fun H => (v H : ℝ)) (h := fun H => (h H : ℝ))
    (G.left_subset.trans hTX) (G.right_subset.trans hTX) G.left_nonempty G.right_nonempty
    hW he hdensity hgap hsize₁ hsize₂ (fun η _ => joiningGroups_alternative G hTX η)

end ESVerify
