import ESVerify.RankWordAdapter
import ESVerify.PlanarRankPaths
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace ESVerify

open Finset

private theorem largeFiber {α β : Type*} [DecidableEq α] [Fintype β]
    [DecidableEq β] [Nonempty β] (s : Finset α) (hs : s.Nonempty) (f : α → β) :
    ∃ t ⊆ s, t.Nonempty ∧
      (s.card : ℝ) / t.card ≤ Fintype.card β ∧
      ∀ p ∈ t, ∀ q ∈ t, f p = f q := by
  let n : ℝ := Fintype.card β
  have hn : 0 < n := by unfold n; exact_mod_cast Fintype.card_pos
  have hcount :
      (Finset.univ : Finset β).card • ((s.card : ℝ) / n) ≤
        ∑ x ∈ s, (1 : ℝ) := by
    rw [nsmul_eq_mul, Finset.card_univ]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    change n * ((s.card : ℝ) / n) ≤ s.card
    rw [mul_div_cancel₀ _ hn.ne']
  obtain ⟨b, _, hb⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := s) (t := (Finset.univ : Finset β)) (f := f) (w := fun _ => (1 : ℝ))
      (by simp) Finset.univ_nonempty hcount
  let t := s.filter fun a => f a = b
  have ht : (s.card : ℝ) / n ≤ t.card := by
    simpa [t, nsmul_eq_mul] using hb
  have hpos : 0 < (t.card : ℝ) :=
    (div_pos (by exact_mod_cast hs.card_pos) hn).trans_le ht
  refine ⟨t, Finset.filter_subset _ _, Finset.card_pos.mp (by exact_mod_cast hpos),
    ?_, ?_⟩
  · change (s.card : ℝ) / t.card ≤ n
    exact (div_le_iff₀ hpos).mpr (by
      rw [mul_comm]
      exact (div_le_iff₀ hn).mp ht)
  · intro p hp q hq
    exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm

/-- Marks at the first attainment of each energy level give a large common-height class.
H and E are the center curve and its cumulative energy at integer times. -/
theorem thinAtEnergyLevels {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (v : ℕ) (Y : α → ℕ → ℤ) (H E : ℕ → ℝ)
    (d z : ℝ) (hz : 0 < z) (hd : d ≤ z / 64)
    (hY0 : ∀ p, Y p 0 = 0)
    (hY : ∀ p ∈ s, ∀ i ≤ v, ∀ j ≤ v,
        |(Y p j : ℝ) - (Y p i : ℝ)| ≤ |(j : ℝ) - i|)
    (hclose : ∀ p ∈ s, ∀ i ≤ v, |(Y p i : ℝ) - H i| ≤ 4 * d)
    (hEnonneg : ∀ i, 0 ≤ E i)
    (hEmono : Monotone E)
    (hCS : ∀ i j : ℕ, i ≤ j → j ≤ v →
      |H j - H i| ^ 2 ≤ ((j : ℝ) - i) * (E j - E i)) :
    ∃ t ⊆ s, t.Nonempty ∧
      Real.logb 2 (s.card : ℝ) - Real.logb 2 (t.card : ℝ) ≤
        (4 * E v / z + 1) * Real.logb 2 (2 * (v : ℝ) + 1) ∧
      ∀ p ∈ t, ∀ q ∈ t, ∀ i ≤ v, ∀ j ≤ v,
        |(j : ℝ) - i| < (Y q j : ℝ) - (Y p i : ℝ) →
          (Y q j : ℝ) - (Y p i : ℝ) < z / 2 := by
  classical
  let r (i : ℕ) := ⌊4 * E i / z⌋₊
  have hr : Monotone r := fun _ _ hij =>
    Nat.floor_mono (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hEmono hij) (by norm_num)) hz.le)
  have hex (l : Fin (r v + 1)) : ∃ k : ℕ, l.val ≤ r k :=
    ⟨v, Nat.le_of_lt_succ l.isLt⟩
  let mark (l : Fin (r v + 1)) := Nat.find (hex l)
  have hmark_le (l : Fin (r v + 1)) : mark l ≤ v :=
    Nat.find_min' _ (Nat.le_of_lt_succ l.isLt)
  have hmark_spec (l : Fin (r v + 1)) : l.val ≤ r (mark l) := Nat.find_spec (hex l)
  let label (p : α) (l : Fin (r v + 1)) : Fin (2 * v + 1) :=
    ⟨(Y p (mark l) + v).toNat % (2 * v + 1), Nat.mod_lt _ (by omega)⟩
  have hlabel {p q : α} (hp : p ∈ s) (hq : q ∈ s) (l : Fin (r v + 1))
      (heq : label p l = label q l) : Y p (mark l) = Y q (mark l) := by
    have hbound (a : α) (ha : a ∈ s) :
        -(v : ℤ) ≤ Y a (mark l) ∧ Y a (mark l) ≤ (v : ℤ) := by
      have hy := hY a ha 0 (Nat.zero_le _) (mark l) (hmark_le l)
      simp only [hY0, Int.cast_zero, Nat.cast_zero, sub_zero,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (mark l))] at hy
      have hv : (mark l : ℝ) ≤ (v : ℝ) := by exact_mod_cast hmark_le l
      have hYr := abs_le.mp (hy.trans hv)
      exact ⟨by exact_mod_cast hYr.1, by exact_mod_cast hYr.2⟩
    have hl (a : α) (ha : a ∈ s) :
        (Y a (mark l) + v).toNat < 2 * v + 1 := by
      have hb := hbound a ha
      omega
    have hv := congrArg Fin.val heq
    dsimp [label] at hv
    rw [Nat.mod_eq_of_lt (hl p hp), Nat.mod_eq_of_lt (hl q hq)] at hv
    have hp' := hbound p hp
    have hq' := hbound q hq
    omega
  obtain ⟨t, hts, ht, hcount, hequal⟩ := largeFiber s hs label
  refine ⟨t, hts, ht, ?_, ?_⟩
  · rw [← Real.logb_div (by exact_mod_cast hs.card_pos.ne') (by exact_mod_cast ht.card_pos.ne')]
    have hc : ((s.card : ℝ) / t.card) ≤ ((2 : ℝ) * v + 1) ^ (r v + 1) := by
      simpa [Fintype.card_fun] using hcount
    have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2)
      (div_pos (by exact_mod_cast hs.card_pos) (by exact_mod_cast ht.card_pos)) hc
    rw [Real.logb_pow] at hlog
    have hrbound : ((r v + 1 : ℕ) : ℝ) ≤ 4 * E v / z + 1 := by
      have hf : (r v : ℝ) ≤ 4 * E v / z :=
        Nat.floor_le (div_nonneg (mul_nonneg (by norm_num) (hEnonneg v)) hz.le)
      push_cast
      linarith
    exact hlog.trans (mul_le_mul_of_nonneg_right hrbound
      (Real.logb_nonneg (by norm_num)
        (by linarith [Nat.cast_nonneg (α := ℝ) v])))
  · intro p hp q hq i hi j hj hdiff
    have hp' := hts hp
    have hq' := hts hq
    have hsame : r i = r j := by
      by_contra hne
      have markBetween (a b : ℕ) (hab : r a < r b) (hb : b ≤ v) :
          ∃ l : Fin (r v + 1), a ≤ mark l ∧ mark l ≤ b := by
        let l : Fin (r v + 1) := ⟨r b, Nat.lt_succ_of_le (hr hb)⟩
        refine ⟨l, ?_, Nat.find_min' _ (le_refl (r b))⟩
        by_contra! h
        exact (not_le_of_gt hab) ((hmark_spec l).trans (hr h.le))
      have commonHeight (l : Fin (r v + 1)) :
          (Y p (mark l) : ℝ) = (Y q (mark l) : ℝ) := by
        exact_mod_cast hlabel hp' hq' l (congrFun (hequal p hp q hq) l)
      have htriangle (l : Fin (r v + 1)) :
          (Y q j : ℝ) - (Y p i : ℝ) ≤
            |(j : ℝ) - mark l| + |(mark l : ℝ) - i| := by
        have h₁ := (le_abs_self _).trans (hY q hq' (mark l) (hmark_le l) j hj)
        have h₂ := (le_abs_self _).trans (hY p hp' i hi (mark l) (hmark_le l))
        linarith [commonHeight l]
      rcases lt_or_gt_of_ne hne with hij | hji
      · obtain ⟨l, hal, hlb⟩ := markBetween i j hij hj
        have hal' : (i : ℝ) ≤ mark l := by exact_mod_cast hal
        have hlb' : (mark l : ℝ) ≤ j := by exact_mod_cast hlb
        have hh := htriangle l
        rw [abs_of_nonneg (sub_nonneg.mpr hlb'), abs_of_nonneg (sub_nonneg.mpr hal')] at hh
        rw [abs_of_nonneg (sub_nonneg.mpr (hal'.trans hlb'))] at hdiff
        linarith
      · obtain ⟨l, hal, hlb⟩ := markBetween j i hji hi
        have hal' : (j : ℝ) ≤ mark l := by exact_mod_cast hal
        have hlb' : (mark l : ℝ) ≤ i := by exact_mod_cast hlb
        have hh := htriangle l
        rw [abs_of_nonpos (sub_nonpos.mpr hal'), abs_of_nonpos (sub_nonpos.mpr hlb')] at hh
        rw [abs_of_nonpos (sub_nonpos.mpr (hal'.trans hlb'))] at hdiff
        linarith
    have hsmall {a b : ℕ} (hab : a ≤ b) (hb : b ≤ v) (heq : r a = r b) :
        |H b - H a| ≤ z / 8 + ((b : ℝ) - a) / 2 := by
      have haFloor : (r a : ℝ) ≤ 4 * E a / z :=
        Nat.floor_le (div_nonneg (mul_nonneg (by norm_num) (hEnonneg a)) hz.le)
      have hbFloor : 4 * E b / z < (r b : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [← heq] at hbFloor
      have henergy : E b - E a ≤ z / 4 := by
        have hab' : 4 * E b / z ≤ 4 * E a / z + 1 := by linarith
        have := (div_le_iff₀ hz).mp hab'
        field_simp at this
        linarith
      have hgap : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
      have hsq := (hCS a b hab hb).trans (mul_le_mul_of_nonneg_left henergy hgap)
      have hhalf : 0 ≤ z / 8 + ((b : ℝ) - a) / 2 := by positivity
      apply (sq_le_sq₀ (abs_nonneg _) hhalf).mp
      nlinarith [sq_nonneg (z / 8 - ((b : ℝ) - a) / 2)]
    have hsmall' : |H j - H i| ≤ z / 8 + |(j : ℝ) - i| / 2 := by
      rcases le_total i j with hij | hji
      · rw [abs_of_nonneg (show 0 ≤ (j : ℝ) - i from
          sub_nonneg.mpr (by exact_mod_cast hij))]
        exact hsmall hij hj hsame
      · rw [abs_sub_comm (H j) (H i), abs_sub_comm (j : ℝ) (i : ℝ),
          abs_of_nonneg (show 0 ≤ (i : ℝ) - j from
            sub_nonneg.mpr (by exact_mod_cast hji))]
        exact hsmall hji hi hsame.symm
    have hqBound := (abs_le.mp (hclose q hq' j hj)).2
    have hpBound := (abs_le.mp (hclose p hp' i hi)).1
    have hcurve := (le_abs_self (H j - H i)).trans hsmall'
    linarith

/-- The explicit estimates for the approximation width and energy in Proposition 5.1. -/
theorem rankApproximationBounds (V v : ℕ) (z δ : ℝ) (hv : v ≤ V)
    (hz : 128 ≤ z) (hδ : 0 ≤ δ) (hδz : δ ≤ z) (hVz : (V : ℝ) ≤ z ^ 3 / 1048576) :
    let d := ⌊z / 64⌋₊
    let E₀ := 64 * (v : ℝ) / (d : ℝ)^2 + 8 * (δ + 1) * Real.log 2
    0 < d ∧ (d : ℝ) ≤ z / 64 ∧ E₀ ≤ 17 * z ∧
      Real.sqrt ((v : ℝ) * E₀) / d ≤ 640 * Real.sqrt ((V : ℝ) / z) := by
  dsimp only
  let d := ⌊z / 64⌋₊
  let E₀ := 64 * (v : ℝ) / (d : ℝ)^2 + 8 * (δ + 1) * Real.log 2
  have hzpos : 0 < z := by linarith
  have hdLower : z / 128 ≤ (d : ℝ) := by
    have h := Nat.lt_floor_add_one (z / 64)
    change z / 64 < (d : ℝ) + 1 at h
    linarith
  have hdPos : 0 < (d : ℝ) := (by positivity : 0 < z / 128).trans_le hdLower
  have hvV : (v : ℝ) ≤ V := by exact_mod_cast hv
  have hmain : 64 * (v : ℝ) / (d : ℝ)^2 ≤ z := by
    apply (div_le_iff₀ (sq_pos_of_pos hdPos)).mpr
    calc
      64 * (v : ℝ) ≤ 64 * (V : ℝ) := by gcongr
      _ ≤ z * (z / 128)^2 := by nlinarith only [hVz]
      _ ≤ z * (d : ℝ)^2 := by
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (by positivity) hdPos.le).mpr hdLower) hzpos.le
  have hterm : 8 * (δ + 1) * Real.log 2 ≤ 16 * z := by
    calc
      _ ≤ 8 * (δ + 1) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      _ ≤ _ := by linarith
  have hE : E₀ ≤ 17 * z := by dsimp [E₀]; linarith
  have hroot : Real.sqrt ((v : ℝ) * E₀) ≤ 5 * Real.sqrt ((V : ℝ) / z) * z := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    calc
      (v : ℝ) * E₀ ≤ (v : ℝ) * (17 * z) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ (V : ℝ) * (17 * z) := mul_le_mul_of_nonneg_right hvV (by positivity)
      _ ≤ (V : ℝ) * (25 * z) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ = (5 * Real.sqrt ((V : ℝ) / z) * z)^2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        field_simp
        ring
  refine ⟨by exact_mod_cast hdPos, Nat.floor_le (by positivity), hE, ?_⟩
  apply (div_le_iff₀ hdPos).mpr
  calc
    _ ≤ 5 * Real.sqrt ((V : ℝ) / z) * z := hroot
    _ = Real.sqrt ((V : ℝ) / z) * (5 * z) := by ring
    _ ≤ Real.sqrt ((V : ℝ) / z) * (640 * (d : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ = 640 * Real.sqrt ((V : ℝ) / z) * (d : ℝ) := by ring

private theorem rankDifferenceSetup (V v n : ℕ) (hV : 1 ≤ V)
    (hcard : Real.logb 2 (n : ℝ) ≤ v) :
    let W := (16384 : ℝ) * (V : ℝ) ^ (1 / 3 : ℝ)
    let δ := (v : ℝ) - Real.logb 2 (n : ℝ)
    let z := W + δ
    128 ≤ z ∧ 0 ≤ δ ∧ δ ≤ z ∧ (V : ℝ) ≤ z ^ 3 / 1048576 := by
  let W := (16384 : ℝ) * (V : ℝ) ^ (1 / 3 : ℝ)
  let δ := (v : ℝ) - Real.logb 2 (n : ℝ)
  let z := W + δ
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hW : 16384 ≤ W := by
    unfold W
    have h := Real.one_le_rpow hVr (by norm_num : (0 : ℝ) ≤ 1 / 3)
    linarith
  have hδ : 0 ≤ δ := sub_nonneg.mpr hcard
  have hWz : W ≤ z := by dsimp [z]; linarith
  have hpow : ((V : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (V : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hzpow : 1048576 * (V : ℝ) ≤ z ^ 3 := calc
    _ ≤ (16384 : ℝ) ^ (3 : ℕ) * (V : ℝ) := by nlinarith
    _ = W ^ 3 := by rw [show W = _ from rfl, mul_pow, hpow]
    _ ≤ z ^ 3 := pow_le_pow_left₀ (by linarith) hWz 3
  exact ⟨by linarith, hδ, by change δ ≤ W + δ; linarith, by linarith⟩

private theorem rankDifferenceLogBudget (V v : ℕ) (z E₀ E C d : ℝ)
    (hV : 1 ≤ V) (hv : v ≤ V) (hz : 0 < z) (hC : 0 ≤ C) (hE : E ≤ 17 * z)
    (hroot : Real.sqrt ((v : ℝ) * E₀) / d ≤ 640 * Real.sqrt ((V : ℝ) / z)) :
    C * (1 + Real.sqrt ((v : ℝ) * E₀) / d) +
      (4 * E / z + 1) * Real.logb 2 (2 * (v : ℝ) + 1) ≤
        (640 * C + 138) * (Real.sqrt ((V : ℝ) / z) + Real.logb 2 ((V : ℝ) + 2)) := by
  let R := Real.sqrt ((V : ℝ) / z)
  let L := Real.logb 2 ((V : ℝ) + 2)
  have hvV : (v : ℝ) ≤ V := by exact_mod_cast hv
  have hV' : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hv' : (0 : ℝ) ≤ v := by positivity
  have hL : 1 ≤ L := by
    unfold L
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hlog : Real.logb 2 (2 * (v : ℝ) + 1) ≤ 2 * L := calc
    _ ≤ Real.logb 2 (((V : ℝ) + 2) ^ (2 : ℕ)) := by
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      nlinarith [sq_nonneg (V : ℝ)]
    _ = 2 * L := by rw [Real.logb_pow]; norm_num [L]
  have hfactor : 4 * E / z + 1 ≤ 69 := by
    have hediv : 4 * E / z ≤ 68 := (div_le_iff₀ hz).2 (by linarith)
    linarith
  have h₁ : C * (1 + Real.sqrt ((v : ℝ) * E₀) / d) ≤ 640 * C * (R + L) := calc
    _ ≤ C * (1 + 640 * R) := mul_le_mul_of_nonneg_left (by linarith only [hroot]) hC
    _ ≤ C * (640 * (R + L)) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by ring
  have h₂ : (4 * E / z + 1) * Real.logb 2 (2 * (v : ℝ) + 1) ≤ 138 * (R + L) := calc
    _ ≤ 69 * Real.logb 2 (2 * (v : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_right hfactor
      exact Real.logb_nonneg (by norm_num) (by linarith)
    _ ≤ 69 * (2 * L) := mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ ≤ _ := by linarith
  calc
    _ ≤ 640 * C * (R + L) + 138 * (R + L) := add_le_add h₁ h₂
    _ = _ := by ring

/-- The path-only version of Proposition 5.1, with an explicit loss constant. -/
theorem rankDifferenceSignWords (hkilled : KilledWalkEstimate)
    (hTalagrand : TalagrandCubeEstimate) {K : ℝ}
    (hEntropy : AnchoredEnergyEntropy K) (hK : 0 ≤ K)
    {V v : ℕ} (hV : 1 ≤ V) (hv : v ≤ V)
    (Ω : Finset (SignWord v)) (hΩ : Ω.Nonempty) :
    let z := (16384 : ℝ) * (V : ℝ) ^ (1 / 3 : ℝ) +
      ((v : ℝ) - Real.logb 2 Ω.card)
    ∃ T ⊆ Ω, T.Nonempty ∧
      Real.logb 2 (Ω.card : ℝ) - Real.logb 2 (T.card : ℝ) ≤
        (640 * (K + 1) + 138) * (Real.sqrt ((V : ℝ) / z) + Real.logb 2 ((V : ℝ) + 2)) ∧
      ∀ w ∈ T, ∀ u ∈ T, ∀ i ≤ v, ∀ j ≤ v,
        |(j : ℝ) - i| < pathHeight (signVec u) j - pathHeight (signVec w) i →
          pathHeight (signVec u) j - pathHeight (signVec w) i < z / 2 := by
  let δ := (v : ℝ) - Real.logb 2 Ω.card
  let z := (16384 : ℝ) * (V : ℝ) ^ (1 / 3 : ℝ) + δ
  have hΩpos : 0 < (Ω.card : ℝ) := by exact_mod_cast hΩ.card_pos
  have hΩcard : Ω.card ≤ 2 ^ v := by
    simpa [SignWord, Fintype.card_fun, Fintype.card_bool] using Finset.card_le_univ Ω
  have hΩcard' : (Ω.card : ℝ) ≤ (2 : ℝ) ^ v := by exact_mod_cast hΩcard
  have hlogCard := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hΩpos hΩcard'
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlogCard
  obtain ⟨hz, hδ, hδz, hVz⟩ := rankDifferenceSetup V v Ω.card hV hlogCard
  let d := ⌊z / 64⌋₊
  let E₀ := approximationEnergy Ω d
  obtain ⟨hd, hdBound, hE₀, hroot⟩ := rankApproximationBounds V v z δ hv hz hδ hδz hVz
  have hzpos : 0 < z := by linarith
  obtain ⟨F, hFΩ, hF, a, ha, hclose, hFCard⟩ :=
    energyApproximation hkilled hTalagrand hEntropy hd Ω hΩ
  obtain ⟨T, hTF, hT, hTCard, hdiff⟩ :=
    thinAtEnergyLevels F hF v signHeight (pathHeight a) (energy a)
      (d : ℝ) z hzpos hdBound
      (fun w => by simp [signHeight])
      (fun w _ i _ j _ => by simpa only [signHeight_cast] using signPrefix_lipschitz w i j)
      (fun w hw i hi => by simpa only [signHeight_cast] using hclose w hw i hi)
      (energy_nonneg a) (energy_mono a)
      (fun i j hij _ => by simpa only [Nat.cast_sub hij] using prefix_diff_sq_le a hij)
  refine ⟨T, hTF.trans hFΩ, hT, ?_, ?_⟩
  · rw [Real.logb_div hΩpos.ne' (by exact_mod_cast hF.card_pos.ne')] at hFCard
    have hbudget :=
      rankDifferenceLogBudget V v z E₀ (energy a v) (K + 1) (d : ℝ)
        hV hv hzpos (by linarith) (ha.trans hE₀) hroot
    have hsum := add_le_add hFCard hTCard
    exact (by linarith only [hsum] : _ ≤ _).trans hbudget
  · simpa only [signHeight_cast] using hdiff

/-- Proposition 5.1 transferred along an injective encoding by sign words. -/
theorem rankDifferenceFromEncoding {α : Type*} [DecidableEq α]
    (hkilled : KilledWalkEstimate) (hTalagrand : TalagrandCubeEstimate) {K : ℝ}
    (hEntropy : AnchoredEnergyEntropy K) (hK : 0 ≤ K)
    {V v : ℕ} (hV : 1 ≤ V) (hv : v ≤ V)
    (X : Finset α) (hX : X.Nonempty) (word : α → SignWord v)
    (hword : Set.InjOn word (X : Set α))
    (leftOf : α → α → Prop) (D : α → α → ℝ)
    (hjoin : ∀ p ∈ X, ∀ q ∈ X, leftOf p q →
      ∃ i ≤ v, ∃ j ≤ v,
        D p q = pathHeight (signVec (word q)) j - pathHeight (signVec (word p)) i ∧
          |(j : ℝ) - i| < D p q) :
    let z := (16384 : ℝ) * (V : ℝ) ^ (1 / 3 : ℝ) +
      ((v : ℝ) - Real.logb 2 X.card)
    ∃ T ⊆ X, T.Nonempty ∧
      Real.logb 2 (X.card : ℝ) - Real.logb 2 (T.card : ℝ) ≤
        (640 * (K + 1) + 138) * (Real.sqrt ((V : ℝ) / z) + Real.logb 2 ((V : ℝ) + 2)) ∧
      ∀ p ∈ T, ∀ q ∈ T, leftOf p q → D p q ≤ z / 2 := by
  classical
  let Ω := X.image word
  have hΩ : Ω.Nonempty := Finset.Nonempty.image hX _
  have hΩCard : Ω.card = X.card := Finset.card_image_of_injOn hword
  have h := rankDifferenceSignWords hkilled hTalagrand hEntropy hK hV hv Ω hΩ
  dsimp only at h
  rw [hΩCard] at h
  obtain ⟨S, hSΩ, hS, hSCard, hgap⟩ := h
  let T := X.filter fun p => word p ∈ S
  have hTImage : T.image word = S := by
    ext w
    constructor
    · intro hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hp).2
    · intro hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (hSΩ hw)
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hw⟩, rfl⟩
  have hTX : T ⊆ X := Finset.filter_subset _ _
  have hTCard : T.card = S.card := by
    rw [← hTImage]
    exact (Finset.card_image_of_injOn
      (fun _ hp _ hq heq => hword (hTX hp) (hTX hq) heq)).symm
  have hT : T.Nonempty := Finset.card_pos.mp (hTCard ▸ hS.card_pos)
  refine ⟨T, hTX, hT, ?_, ?_⟩
  · simpa only [hTCard] using hSCard
  · intro p hp q hq hpq
    obtain ⟨i, hi, j, hj, heq, hij⟩ := hjoin p (hTX hp) q (hTX hq) hpq
    rw [heq] at hij ⊢
    exact (hgap (word p) (Finset.mem_filter.mp hp).2 (word q)
      (Finset.mem_filter.mp hq).2 i hi j hj hij).le

/-- Proposition 5.1 for the cap and cup ranks of Proposition 2.3. -/
theorem rankDifferenceOfRanks {α ι : Type*} [DecidableEq α] [LinearOrder ι]
    (hkilled : KilledWalkEstimate) (hTalagrand : TalagrandCubeEstimate) {K : ℝ}
    (hEntropy : AnchoredEnergyEntropy K) (hK : 0 ≤ K)
    {V A B : ℕ} (hV : 1 ≤ V) (hv : A + B ≤ V)
    (X : Finset α) (hX : X.Nonempty)
    (cap cup : α → ι → ℕ) (slope : α → α → ι) (leftOf : α → α → Prop)
    (side : ∀ p q, p ≠ q → leftOf p q ∨ leftOf q p)
    (cap_le : ∀ p t, cap p t ≤ A) (cup_le : ∀ p t, cup p t ≤ B)
    (cap_anti : ∀ p, Antitone (cap p)) (cup_mono : ∀ p, Monotone (cup p))
    (extension : ∀ p q, leftOf p q →
      cap p (slope p q) < cap q (slope p q) ∧ cup p (slope p q) < cup q (slope p q)) :
    let z := (16384 : ℝ) * (V : ℝ) ^ (1 / 3 : ℝ) +
      (((A + B : ℕ) : ℝ) - Real.logb 2 X.card)
    ∃ T ⊆ X, T.Nonempty ∧
      Real.logb 2 (X.card : ℝ) - Real.logb 2 (T.card : ℝ) ≤
        (640 * (K + 1) + 138) * (Real.sqrt ((V : ℝ) / z) + Real.logb 2 ((V : ℝ) + 2)) ∧
      ∀ p ∈ T, ∀ q ∈ T, leftOf p q →
        let t := slope p q
        (cap q t : ℝ) + cup q t - ((cap p t : ℝ) + cup p t) ≤ z / 2 := by
  obtain ⟨word, hinj, htime, hheight, hgap⟩ :=
    rankPathsBool A B cap cup slope leftOf side cap_le cup_le cap_anti cup_mono extension
  refine rankDifferenceFromEncoding hkilled hTalagrand hEntropy hK hV hv X hX word
    hinj.injOn leftOf (fun p q => (cap q (slope p q) : ℝ) + cup q (slope p q) -
      ((cap p (slope p q) : ℝ) + cup p (slope p q))) ?_
  intro p _ q _ hpq
  refine ⟨_, htime p (slope p q), _, htime q (slope p q), ?_, ?_⟩
  · rw [hheight, hheight]
    ring
  · have hh := hgap p q hpq
    dsimp only at hh ⊢
    rw [hheight, hheight] at hh
    linarith

/-- Proposition 5.1 for a finite point set with distinct abscissae. -/
theorem planar_rankDifference (hkilled : KilledWalkEstimate)
    (hTalagrand : TalagrandCubeEstimate) {K : ℝ}
    (hEntropy : AnchoredEnergyEntropy K) (hK : 0 ≤ K)
    {V : ℕ} (hV : 1 ≤ V) {X : Finset Point} (hX : X.Nonempty)
    (hg : GeneralPosition X) (hx : DistinctAbscissae X) (hv : v X ≤ V) :
    let z := (16384 : ℝ) * (V : ℝ) ^ (1 / 3 : ℝ) +
      ((v X : ℝ) - Real.logb 2 X.card)
    ∃ T ⊆ X, T.Nonempty ∧
      Real.logb 2 (X.card : ℝ) - Real.logb 2 (T.card : ℝ) ≤
        (640 * (K + 1) + 138) * (Real.sqrt ((V : ℝ) / z) + Real.logb 2 ((V : ℝ) + 2)) ∧
      ∀ p ∈ T, ∀ q ∈ T, p.1 < q.1 →
        let t := slope p q
        (endingRank X true q t : ℝ) + endingRank X false q t -
          ((endingRank X true p t : ℝ) + endingRank X false p t) ≤ z / 2 := by
  classical
  have hU : (Finset.univ : Finset (↥X)).Nonempty := by
    obtain ⟨p, hp⟩ := hX
    exact ⟨⟨p, hp⟩, by simp⟩
  obtain ⟨S, _, hS, hSCard, hgap⟩ :=
    rankDifferenceOfRanks hkilled hTalagrand hEntropy hK hV hv Finset.univ hU
      (fun p t => endingRank X true p.val t) (fun p t => endingRank X false p.val t)
      (fun p q => slope p.val q.val) (fun p q => p.val.1 < q.val.1)
      (abscissa_lt_or_gt hx)
      (fun p => endingRank_le_maxLength X true p.val)
      (fun p => endingRank_le_maxLength X false p.val)
      (fun p => endingRank_cap_antitone X p.val)
      (fun p => endingRank_cup_monotone X p.val)
      (fun p q hpq => ⟨endingRank_grows hg true p.property q.property hpq,
        endingRank_grows hg false p.property q.property hpq⟩)
  let T := S.image Subtype.val
  have hTX : T ⊆ X := by
    intro p hp
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.mp hp
    exact p'.property
  have hTCard : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨T, hTX, hS.image _, ?_, ?_⟩
  · simpa only [hTCard, Finset.card_univ, Fintype.card_coe, v] using hSCard
  · intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    simpa only [Finset.card_univ, Fintype.card_coe, v] using hgap p' hp' q' hq' hpq

end ESVerify
