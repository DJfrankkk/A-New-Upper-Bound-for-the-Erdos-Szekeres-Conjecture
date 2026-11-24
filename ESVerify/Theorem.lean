import ESVerify.JoiningAlternative
import ESVerify.PlanarBound
import ESVerify.RankDifference

/-! Assembly of the Erdős–Szekeres cube-root bound. -/

set_option autoImplicit false

noncomputable section

namespace ESVerify

private theorem slope_ne_of_three_points {X : Finset Point}
    (hg : GeneralPosition X) {a b q : Point}
    (ha : a ∈ X) (hb : b ∈ X) (hq : q ∈ X)
    (hab : a.1 < b.1) (hqa : q.1 ≠ a.1) (hqb : q.1 ≠ b.1) :
    slope a q ≠ slope a b := by
  intro hs
  have hab' : a ≠ b := fun e => hab.ne (congrArg Prod.fst e)
  have haq' : a ≠ q := fun e => hqa (congrArg Prod.fst e).symm
  have hbq' : b ≠ q := fun e => hqb (congrArg Prod.fst e).symm
  apply hg a ha b hb q hq hab' haq' hbq'
  unfold slope at hs
  field_simp [sub_ne_zero.mpr hqa, ne_of_gt (sub_pos.mpr hab)] at hs
  unfold orientation
  linarith [hs]

private theorem joiningGroupBudget {T G : Finset Point} {V : ℕ}
    (hV : 2 ≤ V) (hT : T.Nonempty) (hG : G.Nonempty)
    (hle : T.card ≤ 12 * (V + 1)^2 * 4^partitionRounds V * G.card) :
    1 + logCard T - logCard G ≤ 15 * Real.logb 2 ((V : ℝ) + 2) := by
  have hg : (0 : ℝ) < G.card := by exact_mod_cast hG.card_pos
  have ht : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hl := joining_group_log_loss hV hT.card_pos hG.card_pos hle
  rw [Real.logb_div (by positivity) hg.ne', Real.logb_mul (by norm_num) ht.ne',
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hl
  exact hl

private theorem planar_thinning_step (hkilled : KilledWalkEstimate)
    (htal : TalagrandCubeEstimate) {K : ℝ} (hK : 0 ≤ K)
    (hentropy : AnchoredEnergyEntropy K)
    (hequip : ∀ X : Finset Point, GeneralPosition X → DistinctAbscissae X →
      TwoLineEquipartition Prod.fst Prod.snd X)
    {P : Finset Point} (hg : GeneralPosition P) (hx : DistinctAbscissae P)
    (hV : 2 ^ 21 ≤ v P) :
    ThinningStep (fun X => (v X : ℝ)) (fun X => (h X : ℝ)) P (v P)
      (cubeRootReserve (v P)) (640 * (K + 1) + 138 + 15)
      (Real.logb 2 ((v P : ℝ) + 2)) := by
  intro X hXP hX
  let V := v P
  let W := cubeRootReserve (V : ℝ)
  let L := Real.logb 2 ((V : ℝ) + 2)
  let z := slack (fun S => (v S : ℝ)) W X
  let c := 640 * (K + 1) + 138
  let e := thinningCost V (c + 15) L z
  have hV₁ : 1 ≤ V := by dsimp [V]; omega
  have hV₂ : 2 ≤ V := by dsimp [V]; omega
  have hV' : (1 : ℝ) ≤ V := by exact_mod_cast hV₁
  have hW : 0 < W := by unfold W cubeRootReserve; positivity
  have hgX : GeneralPosition X := fun p hp q hq r hr =>
    hg p (hXP hp) q (hXP hq) r (hXP hr)
  have hxX : DistinctAbscissae X := hx.mono hXP
  have hdensity := planar_log_card_le_v hX hgX hxX
  have hz : 0 < z := by
    change 0 < W + (v X : ℝ) - Real.logb 2 X.card
    linarith
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) (by linarith [hV'])
  have he : 0 ≤ e := by unfold e thinningCost c; positivity
  obtain ⟨T, hTX, hT, hcost, hgap⟩ :=
    planar_rankDifference hkilled htal hentropy hK hV₁ hX hgX hxX (v_mono hXP)
  have hcost' : logCard X - logCard T ≤ c * (Real.sqrt ((V : ℝ) / z) + L) := by
    unfold z slack W cubeRootReserve c L logCard
    simpa only [V, add_sub_assoc] using hcost
  change logCard X ≤ (h X : ℝ) + W + 4 * e ∨
    ∃ H ⊂ X, H.Nonempty ∧ logCard X - logCard H ≤ e ∧
      slack (fun S => (v S : ℝ)) W H < (7 / 8) * z
  by_cases hT₂ : 2 ≤ T.card
  · let k := partitionRounds V
    obtain ⟨G⟩ := proposition32 Prod.fst Prod.snd X T
      (endingRank X true) (endingRank X false) (maxLength X true) (maxLength X false)
      V k hTX hT₂ hxX
      (fun a ha b hb q hq => slope_ne_of_three_points hgX ha hb hq)
      (fun p _ => endingRank_cap_antitone X p) (fun p _ => endingRank_cup_monotone X p)
      (fun p _ => endingRank_le_maxLength X true p)
      (fun p _ => endingRank_le_maxLength X false p)
      (v_mono hXP) (fun a ha b hb => endingRank_grows hgX true ha hb)
      (hequip X hgX hxX) (partitionRounds_spec hV₁)
    have hsize₁ : 1 + Real.logb 2 X.card - Real.logb 2 G.left.card ≤ e := by
      have H := joiningGroupBudget hV₂ hT G.left_nonempty G.left_card
      unfold e thinningCost
      change 1 + logCard X - logCard G.left ≤ _
      linarith [Real.sqrt_nonneg ((V : ℝ) / z)]
    have hsize₂ : 1 + Real.logb 2 X.card - Real.logb 2 G.right.card ≤ e := by
      have H := joiningGroupBudget hV₂ hT G.right_nonempty G.right_card
      unfold e thinningCost
      change 1 + logCard X - logCard G.right ≤ _
      linarith [Real.sqrt_nonneg ((V : ℝ) / z)]
    have hgap' : G.rankGap ≤ (W + (v X : ℝ) - Real.logb 2 X.card) / 2 := by
      obtain ⟨p, hp⟩ := G.left_nonempty
      obtain ⟨q, hq⟩ := G.right_nonempty
      have hg' := hgap p (G.left_subset hp) q (G.right_subset hq) (G.ordered p hp q hq)
      dsimp only at hg'
      obtain ⟨hp₁, hp₂⟩ := G.left_rank p hp q hq
      obtain ⟨hq₁, hq₂⟩ := G.right_rank p hp q hq
      change endingRank X true p (slope p q) = G.x₁ at hp₁
      change endingRank X false p (slope p q) = G.y₁ at hp₂
      change endingRank X true q (slope p q) = G.x₂ at hq₁
      change endingRank X false q (slope p q) = G.y₂ at hq₂
      rw [hp₁, hp₂, hq₁, hq₂] at hg'
      simpa only [JoiningGroups.rankGap, W, cubeRootReserve, V, add_sub_assoc] using hg'
    exact joiningGroups_shrink G hTX hW he hdensity hgap' hsize₁ hsize₂
  · left
    have hTc : T.card = 1 := by have := hT.card_pos; omega
    have hcard : logCard T = 0 := by simp [logCard, hTc]
    have hcoef : c * (Real.sqrt ((V : ℝ) / z) + L) ≤ e := by
      unfold e thinningCost
      linarith [Real.sqrt_nonneg ((V : ℝ) / z)]
    have hh : (0 : ℝ) ≤ h X := by positivity
    linarith

/-- Theorem 1.1, with its external concentration, entropy and equipartition
inputs listed explicitly. -/
theorem cube_root_bound_of_estimates
    (hkilled : KilledWalkEstimate) (htal : TalagrandCubeEstimate)
    {K : ℝ} (hK : 0 ≤ K) (hentropy : AnchoredEnergyEntropy K)
    (hequip : ∀ X : Finset Point, GeneralPosition X → DistinctAbscissae X →
      TwoLineEquipartition Prod.fst Prod.snd X) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point, P.Nonempty → GeneralPosition P →
      Real.logb 2 P.card ≤ h P + C * (h P : ℝ) ^ (1 / 3 : ℝ) :=
  planarCubeRootBound
    (fun _ hg hx hX => planar_log_card_le_v hX hg hx)
    (640 * (K + 1) + 138 + 15) (by positivity)
    (fun _ hg hx hV => planar_thinning_step hkilled htal hK hentropy hequip hg hx hV)

end ESVerify
