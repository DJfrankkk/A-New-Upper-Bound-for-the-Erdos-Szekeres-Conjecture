import ESVerify.Planar
import ESVerify.RankPaths

/-! Instantiation of Proposition 2.3 with the planar ending ranks. -/

namespace ESVerify

/-- The order of distinct points is determined by their first coordinates. -/
theorem abscissa_lt_or_gt {X : Finset Point} (hx : DistinctAbscissae X)
    (p q : ↥X) (hpq : p ≠ q) : p.val.1 < q.val.1 ∨ q.val.1 < p.val.1 :=
  lt_or_gt_of_ne (fun h => hpq (Subtype.ext (hx p.property q.property h)))

theorem planar_rankPaths {X : Finset Point} (hg : GeneralPosition X)
    (hx : DistinctAbscissae X) :
    ∃ w : ↥X → Finset (Fin (v X)), Function.Injective w ∧
      (∀ p, (w p).card = maxLength X true) ∧
      (∀ (p : ↥X) (t : ℝ), RankPath.time (maxLength X false)
        (endingRank X true p.val t) (endingRank X false p.val t) ≤ v X) ∧
      (∀ (p : ↥X) (t : ℝ), RankPath.height (w p) (RankPath.time (maxLength X false)
          (endingRank X true p.val t) (endingRank X false p.val t)) =
        (endingRank X true p.val t : ℤ) + (endingRank X false p.val t : ℤ) - maxLength X false) := by
  refine rankPaths (α := ↥X) (ι := ℝ) (maxLength X true) (maxLength X false)
    (fun p t => endingRank X true p.val t) (fun p t => endingRank X false p.val t)
    (fun p q => slope p.val q.val) (fun p q => p.val.1 < q.val.1)
    (abscissa_lt_or_gt hx)
    (fun p => endingRank_le_maxLength X true p.val)
    (fun p => endingRank_le_maxLength X false p.val)
    (fun p => endingRank_cap_antitone X p.val)
    (fun p => endingRank_cup_monotone X p.val) ?_
  intro p q hpq
  exact ⟨endingRank_grows hg true p.property q.property hpq,
    endingRank_grows hg false p.property q.property hpq⟩

theorem planar_card_le_choose {X : Finset Point} (hg : GeneralPosition X)
    (hx : DistinctAbscissae X) : X.card ≤ (v X).choose (maxLength X true) := by
  classical
  obtain ⟨w, hinj, hcard, _, _⟩ := planar_rankPaths hg hx
  simpa [v] using card_le_choose_of_rankPaths (maxLength X true) (maxLength X false) w hinj hcard

theorem planar_card_le_pow {X : Finset Point} (hg : GeneralPosition X)
    (hx : DistinctAbscissae X) : X.card ≤ 2 ^ v X :=
  (planar_card_le_choose hg hx).trans (Nat.choose_le_two_pow (v X) (maxLength X true))

theorem planar_log_card_le_v {X : Finset Point} (hX : X.Nonempty)
    (hg : GeneralPosition X) (hx : DistinctAbscissae X) :
    Real.logb 2 (X.card : ℝ) ≤ (v X : ℝ) := by
  have hp : 0 < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp).mpr
  rw [Real.rpow_natCast]
  exact_mod_cast planar_card_le_pow hg hx

end ESVerify