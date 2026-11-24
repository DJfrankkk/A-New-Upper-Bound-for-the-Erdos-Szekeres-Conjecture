import ESVerify.RankPaths
import ESVerify.EnergyApproximation

/-! Boolean sign words for the passage from Proposition 2.3 to Proposition 5.1. -/

set_option autoImplicit false

namespace ESVerify

namespace RankPath

def word {N : ℕ} (s : Finset (Fin N)) : SignWord N :=
  fun i => decide (i ∈ s)

theorem word_injective {N : ℕ} : Function.Injective (@word N) := by
  intro s t h
  ext i
  simpa [word] using iff_of_eq (congrArg (· = true) (congrFun h i))

private theorem pathHeight_eq_sum_fin {N : ℕ} (a : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    pathHeight a k = ∑ i : Fin N, if i.val < k then a i else 0 := by
  rw [← Finset.sum_filter]
  unfold pathHeight
  symm
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    have hjk := Finset.mem_range.mp hj
    exact ⟨⟨j, hjk.trans_le hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩, rfl⟩
  · intro i _
    rw [atIndex_of_lt a i.isLt]

theorem prefix_word {N : ℕ} (s : Finset (Fin N)) (k : ℕ) (hk : k ≤ N) :
    pathHeight (signVec (word s)) k = (height s k : ℝ) := by
  classical
  have hcount (u : Finset (Fin N)) (c : ℝ) :
      (∑ i ∈ u, if i.val < k then c else 0) = (prefixCard u k : ℝ) * c := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  have hs : (Finset.univ.filter fun i : Fin N => i ∈ s) = s := by
    ext i
    simp
  calc
    pathHeight (signVec (word s)) k =
        ∑ i : Fin N, ((if i ∈ s then (if i.val < k then (2 : ℝ) else 0) else 0)
          - (if i.val < k then (1 : ℝ) else 0)) := by
      rw [pathHeight_eq_sum_fin _ _ hk]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hm : i ∈ s <;> by_cases hi : i.val < k <;>
        norm_num [signVec, word, hm, hi]
    _ = (prefixCard s k : ℝ) * 2 - (k : ℝ) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_filter (fun i => i ∈ s), hs,
        hcount, hcount, prefixCard_univ hk]
      ring
    _ = (height s k : ℝ) := by
      simp only [height, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
      ring

end RankPath

/-- Rank paths as Boolean sign words, with real-valued heights and the strict
separation at a joining slope from equation (3). -/
theorem rankPathsBool {α ι : Type*} [LinearOrder ι] (A B : ℕ)
    (cap cup : α → ι → ℕ) (slope : α → α → ι) (leftOf : α → α → Prop)
    (side : ∀ p q, p ≠ q → leftOf p q ∨ leftOf q p)
    (cap_le : ∀ p t, cap p t ≤ A) (cup_le : ∀ p t, cup p t ≤ B)
    (cap_anti : ∀ p, Antitone (cap p)) (cup_mono : ∀ p, Monotone (cup p))
    (extension : ∀ p q, leftOf p q →
      cap p (slope p q) < cap q (slope p q) ∧ cup p (slope p q) < cup q (slope p q)) :
    ∃ w : α → SignWord (A + B), Function.Injective w ∧
      (∀ p t, RankPath.time B (cap p t) (cup p t) ≤ A + B) ∧
      (∀ p t, pathHeight (signVec (w p)) (RankPath.time B (cap p t) (cup p t)) =
        (cap p t : ℝ) + (cup p t : ℝ) - B) ∧
      (∀ p q, leftOf p q →
        let t := slope p q
        let i := RankPath.time B (cap p t) (cup p t)
        let j := RankPath.time B (cap q t) (cup q t)
        |(j : ℝ) - (i : ℝ)| <
          pathHeight (signVec (w q)) j - pathHeight (signVec (w p)) i) := by
  obtain ⟨s, hs, _, htime, hgt⟩ :=
    rankPaths A B cap cup slope leftOf side cap_le cup_le cap_anti cup_mono extension
  let w (p : α) := RankPath.word (s p)
  have hprefix (p : α) (t : ι) :
      pathHeight (signVec (w p)) (RankPath.time B (cap p t) (cup p t)) =
        (cap p t : ℝ) + (cup p t : ℝ) - B := by
    rw [show w p = RankPath.word (s p) by rfl, RankPath.prefix_word _ _ (htime p t), hgt p t]
    norm_cast
  refine ⟨w, RankPath.word_injective.comp hs, htime, hprefix, ?_⟩
  intro p q hpq
  dsimp
  rw [hprefix, hprefix]
  have hgap := rank_gap_gt_time_distance (cup_le p (slope p q)) (cup_le q (slope p q))
    (extension p q hpq).1 (extension p q hpq).2
  have hgap' : |(RankPath.time B (cap q (slope p q)) (cup q (slope p q)) : ℝ) -
      (RankPath.time B (cap p (slope p q)) (cup p (slope p q)) : ℝ)| <
      (cap q (slope p q) : ℝ) + cup q (slope p q) -
        ((cap p (slope p q) : ℝ) + cup p (slope p q)) := by
    exact_mod_cast hgap
  linarith

end ESVerify

