import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace ESVerify

noncomputable section

/-- An affine equation for a line, or an affine function used to select its sides. -/
structure LineForm where
  dx : ℝ
  dy : ℝ
  c : ℝ

def LineForm.eval (l : LineForm) (x y : ℝ) : ℝ := l.dx * x + l.dy * y + l.c

def LineForm.independent (l₁ l₂ : LineForm) : Prop := l₁.dx * l₂.dy - l₂.dx * l₁.dy ≠ 0

def openSide (s : Bool) (t : ℝ) : Prop := if s then 0 < t else t < 0

variable {α ι : Type*}

/-- The points of a finite set in one open quadrant of two lines. -/
def lineQuadrant (ξ υ : α → ℝ) (E : Finset α) (l₁ l₂ : LineForm)
    (s : Bool × Bool) : Finset α := by
  classical
  exact E.filter fun p ↦ openSide s.1 (l₁.eval (ξ p) (υ p)) ∧
    openSide s.2 (l₂.eval (ξ p) (υ p))

/-- Megiddo's two-line equipartition input (Lemma 3.1). The two lines can be
chosen transverse, as all four open quadrants are required to be nonempty. -/
def TwoLineEquipartition (ξ υ : α → ℝ) (X : Finset α) : Prop :=
  ∀ E ⊆ X, ∀ b : ℕ, 0 < b → E.card = 4 * b →
    ∃ l₁ l₂ : LineForm, l₁.independent l₂ ∧
      ∀ s : Bool × Bool, (lineQuadrant ξ υ E l₁ l₂ s).card = b

private theorem eval_eq (m l₁ l₂ : LineForm) (h : l₁.independent l₂) :
    ∃ a b c : ℝ, ∀ x y : ℝ, m.eval x y = a * l₁.eval x y + b * l₂.eval x y + c := by
  let d := l₁.dx * l₂.dy - l₂.dx * l₁.dy
  let a := (m.dx * l₂.dy - l₂.dx * m.dy) / d
  let b := (l₁.dx * m.dy - m.dx * l₁.dy) / d
  have hd : d ≠ 0 := h
  have hdx : a * l₁.dx + b * l₂.dx = m.dx := by
    dsimp [a, b]
    field_simp
    dsimp [d]
    ring
  have hdy : a * l₁.dy + b * l₂.dy = m.dy := by
    dsimp [a, b]
    field_simp
    dsimp [d]
    ring
  refine ⟨a, b, m.c - a * l₁.c - b * l₂.c, fun x y ↦ ?_⟩
  unfold LineForm.eval
  calc
    _ = (a * l₁.dx + b * l₂.dx) * x + (a * l₁.dy + b * l₂.dy) * y + m.c := by
      rw [hdx, hdy]
    _ = _ := by ring

private theorem mul_nonneg_of_side (a z : ℝ)
    (h : openSide (decide (0 ≤ a)) z) : 0 ≤ a * z := by
  by_cases ha : 0 ≤ a
  · simp [openSide, ha] at h
    exact mul_nonneg ha h.le
  · simp [openSide, ha] at h
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) h.le

private theorem mul_nonpos_of_side (a z : ℝ)
    (h : openSide (decide (a ≤ 0)) z) : a * z ≤ 0 := by
  by_cases ha : a ≤ 0
  · simp [openSide, ha] at h
    exact mul_nonpos_of_nonpos_of_nonneg ha h.le
  · simp [openSide, ha] at h
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_not_ge ha) h.le

/-- A line crosses a finite set when there are points on both its strict sides. -/
def LineCrosses (ξ υ : α → ℝ) (E : Finset α) (m : LineForm) : Prop :=
  (∃ p ∈ E, 0 < m.eval (ξ p) (υ p)) ∧ (∃ p ∈ E, m.eval (ξ p) (υ p) < 0)

private theorem LineCrosses.mono {ξ υ : α → ℝ} {E F : Finset α} {m : LineForm}
    (h : LineCrosses ξ υ E m) (hEF : E ⊆ F) : LineCrosses ξ υ F m := by
  obtain ⟨⟨p, hp, hmp⟩, ⟨q, hq, hmq⟩⟩ := h
  exact ⟨⟨p, hEF hp, hmp⟩, ⟨q, hEF hq, hmq⟩⟩

private theorem exists_quadrant_uncrossed (ξ υ : α → ℝ) (E : Finset α)
    {l₁ l₂ : LineForm} (h : l₁.independent l₂) (m : LineForm) :
    ∃ s, ¬ LineCrosses ξ υ (lineQuadrant ξ υ E l₁ l₂ s) m := by
  classical
  obtain ⟨a, b, c, hm⟩ := eval_eq m l₁ l₂ h
  by_cases hc : 0 ≤ c
  · refine ⟨(decide (0 ≤ a), decide (0 ≤ b)), fun hcross ↦ ?_⟩
    obtain ⟨p, hp, hneg⟩ := hcross.2
    obtain ⟨_, h₁, h₂⟩ := Finset.mem_filter.mp hp
    have ha := mul_nonneg_of_side a (l₁.eval (ξ p) (υ p)) h₁
    have hb := mul_nonneg_of_side b (l₂.eval (ξ p) (υ p)) h₂
    rw [hm] at hneg
    linarith
  · refine ⟨(decide (a ≤ 0), decide (b ≤ 0)), fun hcross ↦ ?_⟩
    obtain ⟨p, hp, hpos⟩ := hcross.1
    obtain ⟨_, h₁, h₂⟩ := Finset.mem_filter.mp hp
    have ha := mul_nonpos_of_side a (l₁.eval (ξ p) (υ p)) h₁
    have hb := mul_nonpos_of_side b (l₂.eval (ξ p) (υ p)) h₂
    rw [hm] at hpos
    linarith [le_of_not_ge hc]

private noncomputable def crossingEntries (ξ υ : α → ℝ) (E : Finset α)
    (L : Finset ι) (line : ι → LineForm) : Finset ι := by
  classical
  exact L.filter fun i ↦ LineCrosses ξ υ E (line i)

private theorem crossingEntries_mono {ξ υ : α → ℝ} {L : Finset ι} {line : ι → LineForm}
    {E F : Finset α} (h : E ⊆ F) :
    crossingEntries ξ υ E L line ⊆ crossingEntries ξ υ F L line := by
  classical
  intro i hi
  obtain ⟨hL, hc⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hL, LineCrosses.mono hc h⟩

private theorem find_sparse_quadrant (ξ υ : α → ℝ) (E : Finset α)
    (L : Finset ι) (line : ι → LineForm) {l₁ l₂ : LineForm} (h : l₁.independent l₂) :
    ∃ s, 4 * (crossingEntries ξ υ (lineQuadrant ξ υ E l₁ l₂ s) L line).card ≤
      3 * (crossingEntries ξ υ E L line).card := by
  classical
  let candidates : Finset (Bool × Bool) := univ
  let L' := crossingEntries ξ υ E L line
  let Q (s : Bool × Bool) := lineQuadrant ξ υ E l₁ l₂ s
  let C (s : Bool × Bool) := crossingEntries ξ υ (Q s) L line
  have hsub (s : Bool × Bool) : C s ⊆ L' := crossingEntries_mono (Finset.filter_subset _ _)
  have hsum : ∑ s ∈ candidates, (C s).card ≤ 3 * L'.card := by
    calc
      _ = ∑ s ∈ candidates, ∑ i ∈ L', if LineCrosses ξ υ (Q s) (line i) then 1 else 0 := by
        apply sum_congr rfl
        intro s hs
        have heq : C s = L'.filter (fun i ↦ LineCrosses ξ υ (Q s) (line i)) := by
          ext i
          simp only [C, L', crossingEntries, mem_filter]
          constructor
          · intro hi
            exact ⟨⟨hi.1, (Finset.mem_filter.mp (hsub s (Finset.mem_filter.mpr hi))).2⟩, hi.2⟩
          · exact fun hi ↦ ⟨hi.1.1, hi.2⟩
        rw [heq, Finset.card_filter]
      _ = ∑ i ∈ L', ∑ s ∈ candidates, if LineCrosses ξ υ (Q s) (line i) then 1 else 0 :=
        Finset.sum_comm
      _ ≤ ∑ _i ∈ L', 3 := by
        apply sum_le_sum
        intro i hi
        rw [← Finset.card_filter]
        obtain ⟨s, hs⟩ := exists_quadrant_uncrossed ξ υ E h (line i)
        have hsub' : candidates.filter (fun j ↦ LineCrosses ξ υ (Q j) (line i)) ⊆
            candidates.erase s := by
          intro j hj
          rw [Finset.mem_erase]
          refine ⟨?_, (Finset.mem_filter.mp hj).1⟩
          rintro rfl
          exact hs (Finset.mem_filter.mp hj).2
        exact (Finset.card_le_card hsub').trans (by simp [candidates])
      _ = _ := by simp [Nat.mul_comm]
  by_contra! hlower
  have hgt : ∑ _s ∈ candidates, 3 * L'.card < ∑ s ∈ candidates, 4 * (C s).card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun s _ ↦ hlower s)
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hgt
  have hfinal : 4 * (3 * L'.card) < 4 * ∑ s ∈ candidates, (C s).card := by
    simpa [candidates, ← Finset.mul_sum] using hgt
  omega

private theorem repeatedly_thin (ξ υ : α → ℝ) (X : Finset α)
    (hequip : TwoLineEquipartition ξ υ X) (L : Finset ι) (line : ι → LineForm)
    (k b : ℕ) (hb : 0 < b) (E : Finset α) (hEX : E ⊆ X) (hE : E.card = b * 4 ^ k) :
    ∃ E' ⊆ E, E'.card = b ∧ 4 ^ k * (crossingEntries ξ υ E' L line).card ≤
      3 ^ k * (crossingEntries ξ υ E L line).card := by
  classical
  induction k generalizing E with
  | zero => exact ⟨E, Subset.rfl, by simpa using hE, by simp⟩
  | succ k ih =>
    have hb' : 0 < b * 4 ^ k := by positivity
    have hE' : E.card = 4 * (b * 4 ^ k) := by rw [hE, pow_succ]; ring
    obtain ⟨l₁, l₂, hind, hcard⟩ := hequip E hEX (b * 4 ^ k) hb' hE'
    obtain ⟨s, hs⟩ := find_sparse_quadrant ξ υ E L line hind
    let Q := lineQuadrant ξ υ E l₁ l₂ s
    have hQE : Q ⊆ E := Finset.filter_subset _ _
    obtain ⟨F, hFQ, hFc, hF⟩ := ih Q (hQE.trans hEX) (hcard s)
    refine ⟨F, hFQ.trans hQE, hFc, ?_⟩
    calc
      _ = 4 * (4 ^ k * (crossingEntries ξ υ F L line).card) := by rw [pow_succ]; ring
      _ ≤ 4 * (3 ^ k * (crossingEntries ξ υ Q L line).card) := Nat.mul_le_mul_left _ hF
      _ = 3 ^ k * (4 * (crossingEntries ξ υ Q L line).card) := by ring
      _ ≤ 3 ^ k * (3 * (crossingEntries ξ υ E L line).card) := Nat.mul_le_mul_left _ hs
      _ = _ := by rw [pow_succ]; ring

/-- Iterate the equipartition until the retained points are separated by only
half as many line entries as there are points in the other group. -/
private theorem thin_crossing_entries (ξ υ : α → ℝ) (X E : Finset α)
    (hequip : TwoLineEquipartition ξ υ X) (hEX : E ⊆ X) (hE : E.Nonempty)
    (L : Finset ι) (line : ι → LineForm) (V k n : ℕ)
    (hL : L.card ≤ V * n) (hk : 2 * V * 3 ^ k ≤ 4 ^ k) :
    ∃ F ⊆ E, F.Nonempty ∧ E.card ≤ 2 * 4 ^ k * F.card ∧
      2 * (crossingEntries ξ υ F L line).card ≤ n := by
  classical
  by_cases hsmall : E.card < 4 ^ k
  · obtain ⟨p, hp⟩ := hE
    refine ⟨{p}, Finset.singleton_subset_iff.mpr hp, Finset.singleton_nonempty _, ?_, ?_⟩
    · simp only [Finset.card_singleton, mul_one]
      omega
    · have hempty : crossingEntries ξ υ {p} L line = ∅ := by
        ext i
        simp only [crossingEntries, mem_filter, notMem_empty, iff_false]
        rintro ⟨_, h⟩
        simp only [LineCrosses, mem_singleton, exists_eq_left] at h
        exact (not_lt_of_ge h.1.le) h.2
      simp [hempty]
  · let r := 4 ^ k
    let b := E.card / r
    have hr : 0 < r := by positivity
    have hb : 0 < b := Nat.div_pos (le_of_not_gt hsmall) hr
    have hbr : b * r ≤ E.card := Nat.div_mul_le_self E.card r
    have hhalf : E.card ≤ 2 * (b * r) := by
      have hb1 : 1 ≤ b := hb
      have hrb : r ≤ b * r := by simpa using Nat.mul_le_mul_right r hb1
      have hmod : E.card % r < r := Nat.mod_lt _ hr
      have hdecomp : E.card % r + b * r = E.card := by
        simpa [b, Nat.mul_comm] using Nat.mod_add_div E.card r
      omega
    obtain ⟨E₀, hE₀E, hE₀c⟩ := Finset.exists_subset_card_eq hbr
    obtain ⟨F, hFE₀, hFc, hcross⟩ :=
      repeatedly_thin ξ υ X hequip L line k b hb E₀ (hE₀E.trans hEX) hE₀c
    refine ⟨F, hFE₀.trans hE₀E, card_pos.mp (hFc ▸ hb), ?_, ?_⟩
    · rw [hFc]
      convert hhalf using 1
      simp only [r]
      ring
    · have hLE : (crossingEntries ξ υ E₀ L line).card ≤ V * n := by
        exact (Finset.card_filter_le _ _).trans hL
      apply (Nat.mul_le_mul_left_iff hr).mp
      calc
        r * (2 * (crossingEntries ξ υ F L line).card) =
            2 * (r * (crossingEntries ξ υ F L line).card) := by ring
        _ ≤ 2 * (3 ^ k * (crossingEntries ξ υ E₀ L line).card) := Nat.mul_le_mul_left _ hcross
        _ ≤ 2 * (3 ^ k * (V * n)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hLE)
        _ = (2 * V * 3 ^ k) * n := by ring
        _ ≤ r * n := Nat.mul_le_mul_right _ hk

/-- Slope in the chosen coordinates. -/
def joiningSlope (ξ υ : α → ℝ) (p q : α) : ℝ := (υ q - υ p) / (ξ q - ξ p)

theorem joiningSlope_comm (ξ υ : α → ℝ) (p q : α) :
    joiningSlope ξ υ p q = joiningSlope ξ υ q p := by
  unfold joiningSlope
  rw [← neg_sub (υ q) (υ p), ← neg_sub (ξ q) (ξ p), neg_div_neg_eq]

def throughSlope (ξ υ : α → ℝ) (p : α) (t : ℝ) : LineForm :=
  ⟨-t, 1, t * ξ p - υ p⟩

theorem throughSlope_eval (ξ υ : α → ℝ) (p q : α) (t : ℝ) (h : ξ q ≠ ξ p) :
    (throughSlope ξ υ p t).eval (ξ q) (υ q) =
      (ξ q - ξ p) * (joiningSlope ξ υ p q - t) := by
  have hd : ξ q - ξ p ≠ 0 := sub_ne_zero.mpr h
  simp only [throughSlope, LineForm.eval, joiningSlope]
  field_simp
  ring

/-- Every point of the first set is strictly to the left of every point of the second. -/
def LeftOf (ξ : α → ℝ) (D E : Finset α) : Prop := ∀ p ∈ D, ∀ q ∈ E, ξ p < ξ q

theorem LeftOf.mono {ξ : α → ℝ} {D E D' E' : Finset α}
    (h : LeftOf ξ D E) (hD : D' ⊆ D) (hE : E' ⊆ E) : LeftOf ξ D' E' :=
  fun p hp q hq ↦ h p (hD hp) q (hE hq)

private def rankCode (x y : α → ℝ → ℕ) (A : ℕ) (p : α) (t : ℝ) : ℕ :=
  (A - x p t) + y p t

private theorem rankCode_mono {x y : α → ℝ → ℕ} {A : ℕ} {p : α}
    (hx : Antitone (x p)) (hy : Monotone (y p)) : Monotone (rankCode x y A p) := by
  intro s t hst
  unfold rankCode
  have hxs := hx hst
  have hys := hy hst
  omega

private theorem rankCode_strict {x y : α → ℝ → ℕ} {A : ℕ} {p : α} {s t : ℝ}
    (hx : Antitone (x p)) (hy : Monotone (y p)) (hA : x p s ≤ A)
    (hst : s ≤ t) (hr : (x p s, y p s) ≠ (x p t, y p t)) :
    rankCode x y A p s < rankCode x y A p t := by
  have hxs := hx hst
  have hys := hy hst
  unfold rankCode
  by_contra! hneg
  apply hr
  exact Prod.ext (by omega) (by omega)

private noncomputable def slopeMarker (S : Finset ℝ) (r : ℝ → ℕ) (c : ℕ) : ℝ := by
  classical
  let low := S.filter fun t ↦ r t ≤ c
  let high := S.filter fun t ↦ c < r t
  exact if hlow : low.Nonempty then
    if hhigh : high.Nonempty then (low.max' hlow + high.min' hhigh) / 2 else 0 else 0

private theorem slopeMarker_between {S : Finset ℝ} {r : ℝ → ℕ} {c : ℕ} {s t : ℝ}
    (hr : Monotone r) (hs : s ∈ S) (ht : t ∈ S) (hrs : r s ≤ c) (hrt : c < r t) :
    s < slopeMarker S r c ∧ slopeMarker S r c < t := by
  classical
  let low := S.filter fun a ↦ r a ≤ c
  let high := S.filter fun a ↦ c < r a
  have hs' : s ∈ low := Finset.mem_filter.mpr ⟨hs, hrs⟩
  have ht' : t ∈ high := Finset.mem_filter.mpr ⟨ht, hrt⟩
  have hlo : low.Nonempty := ⟨s, hs'⟩
  have hhi : high.Nonempty := ⟨t, ht'⟩
  have hsmax := low.le_max' s hs'
  have hmint := high.min'_le t ht'
  have hlt : low.max' hlo < high.min' hhi := by
    by_contra! hn
    have h₁ := (Finset.mem_filter.mp (low.max'_mem hlo)).2
    have h₂ := (Finset.mem_filter.mp (high.min'_mem hhi)).2
    exact (not_le_of_gt h₂) ((hr hn).trans h₁)
  have hmark : slopeMarker S r c = (low.max' hlo + high.min' hhi) / 2 := by
    change (if h : low.Nonempty then if h' : high.Nonempty then
      (low.max' h + high.min' h') / 2 else 0 else 0) = _
    rw [dif_pos hlo, dif_pos hhi]
  rw [hmark]
  constructor <;> linarith

private theorem marker_crosses (ξ υ : α → ℝ) (D E F : Finset α) (p q r : α)
    (hp : p ∈ D) (hq : q ∈ F) (hr : r ∈ F) (hFE : F ⊆ E)
    (hDE : LeftOf ξ D E ∨ LeftOf ξ E D) {t : ℝ}
    (hqt : joiningSlope ξ υ p q < t) (hrt : t < joiningSlope ξ υ p r) :
    LineCrosses ξ υ F (throughSlope ξ υ p t) := by
  rcases hDE with h | h
  · have hξq : 0 < ξ q - ξ p := sub_pos.mpr (h p hp q (hFE hq))
    have hξr : 0 < ξ r - ξ p := sub_pos.mpr (h p hp r (hFE hr))
    refine ⟨⟨r, hr, ?_⟩, ⟨q, hq, ?_⟩⟩
    · rw [throughSlope_eval _ _ _ _ _ (sub_ne_zero.mp hξr.ne')]
      exact mul_pos hξr (sub_pos.mpr hrt)
    · rw [throughSlope_eval _ _ _ _ _ (sub_ne_zero.mp hξq.ne')]
      exact mul_neg_of_pos_of_neg hξq (sub_neg.mpr hqt)
  · have hξq : ξ q - ξ p < 0 := sub_neg.mpr (h q (hFE hq) p hp)
    have hξr : ξ r - ξ p < 0 := sub_neg.mpr (h r (hFE hr) p hp)
    refine ⟨⟨q, hq, ?_⟩, ⟨r, hr, ?_⟩⟩
    · rw [throughSlope_eval _ _ _ _ _ (sub_ne_zero.mp hξq.ne)]
      exact mul_pos_of_neg_of_neg hξq (sub_neg.mpr hqt)
    · rw [throughSlope_eval _ _ _ _ _ (sub_ne_zero.mp hξr.ne)]
      exact mul_neg_of_neg_of_pos hξr (sub_pos.mpr hrt)

private theorem oneDirection (ξ υ : α → ℝ) (X D E : Finset α)
    (x y : α → ℝ → ℕ) (A B V k : ℕ)
    (hx : ∀ p ∈ X, Antitone (x p)) (hy : ∀ p ∈ X, Monotone (y p))
    (hxA : ∀ p ∈ X, ∀ t, x p t ≤ A) (hyB : ∀ p ∈ X, ∀ t, y p t ≤ B)
    (hAB : A + B ≤ V) (hDX : D ⊆ X) (hEX : E ⊆ X)
    (hD : D.Nonempty) (hE : E.Nonempty) (hDE : LeftOf ξ D E ∨ LeftOf ξ E D)
    (hequip : TwoLineEquipartition ξ υ X) (hk : 2 * V * 3 ^ k ≤ 4 ^ k) :
    ∃ D' ⊆ D, ∃ E' ⊆ E, D'.Nonempty ∧ E'.Nonempty ∧
      D.card ≤ 2 * (V + 1)^2 * D'.card ∧ E.card ≤ 2 * 4^k * E'.card ∧
      ∃ a b : ℕ, ∀ p ∈ D', ∀ q ∈ E',
        x p (joiningSlope ξ υ p q) = a ∧ y p (joiningSlope ξ υ p q) = b := by
  classical
  let L := D.product (Finset.range V)
  let slopes (p : α) := E.image (joiningSlope ξ υ p)
  let line (i : α × ℕ) := throughSlope ξ υ i.1 (slopeMarker (slopes i.1) (rankCode x y A i.1) i.2)
  have hLc : L.card ≤ V * D.card := by simp [L, Nat.mul_comm]
  obtain ⟨F, hFE, hFn, hFcard, hcross⟩ :=
    thin_crossing_entries ξ υ X E hequip hEX hE L line V k D.card hLc hk
  let bad := crossingEntries ξ υ F L line
  let removed := bad.image Prod.fst
  let good := D \ removed
  have hremoved : removed ⊆ D := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1
  have hremCard : removed.card ≤ bad.card := Finset.card_image_le
  have hgoodCard : D.card ≤ 2 * good.card := by
    have hpart : good.card + removed.card = D.card := Finset.card_sdiff_add_card_eq_card hremoved
    change 2 * bad.card ≤ D.card at hcross
    omega
  have hgn : good.Nonempty := Finset.card_pos.mp (by have := card_pos.mpr hD; omega)
  have hgood (p : α) (hp : p ∈ good) (q r : α) (hq : q ∈ F) (hr : r ∈ F) :
      (x p (joiningSlope ξ υ p q), y p (joiningSlope ξ υ p q)) =
        (x p (joiningSlope ξ υ p r), y p (joiningSlope ξ υ p r)) := by
    suffices horder : ∀ q r : α, q ∈ F → r ∈ F → joiningSlope ξ υ p q ≤ joiningSlope ξ υ p r →
        (x p (joiningSlope ξ υ p q), y p (joiningSlope ξ υ p q)) =
        (x p (joiningSlope ξ υ p r), y p (joiningSlope ξ υ p r)) by
      rcases le_total (joiningSlope ξ υ p q) (joiningSlope ξ υ p r) with h | h
      · exact horder q r hq hr h
      · exact (horder r q hr hq h).symm
    intro q r hq hr hqr
    by_contra hne
    have hpD : p ∈ D := (Finset.mem_sdiff.mp hp).1
    have hpX : p ∈ X := hDX hpD
    let c := rankCode x y A p (joiningSlope ξ υ p q)
    have hlt : c < rankCode x y A p (joiningSlope ξ υ p r) :=
      rankCode_strict (hx p hpX) (hy p hpX) (hxA p hpX _) hqr hne
    have hbound : rankCode x y A p (joiningSlope ξ υ p r) ≤ V := by
      unfold rankCode
      have := hyB p hpX (joiningSlope ξ υ p r)
      omega
    have hc : c < V := hlt.trans_le hbound
    have hb : (p, c) ∈ L := Finset.mem_product.mpr ⟨hpD, Finset.mem_range.mpr hc⟩
    have hbetween := slopeMarker_between (rankCode_mono (hx p hpX) (hy p hpX))
      (Finset.mem_image_of_mem (joiningSlope ξ υ p) (hFE hq))
      (Finset.mem_image_of_mem (joiningSlope ξ υ p) (hFE hr)) (le_refl c) hlt
    have hsplit : LineCrosses ξ υ F (line (p, c)) :=
      marker_crosses ξ υ D E F p q r hpD hq hr hFE hDE hbetween.1 hbetween.2
    have hbad : (p, c) ∈ bad := Finset.mem_filter.mpr ⟨hb, hsplit⟩
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_image_of_mem Prod.fst hbad)
  obtain ⟨q₀, hq₀⟩ := hFn
  let f (p : α) := (x p (joiningSlope ξ υ p q₀), y p (joiningSlope ξ υ p q₀))
  let colors := (Finset.range (V + 1)).product (Finset.range (V + 1))
  let fiber (c : ℕ × ℕ) := good.filter (fun p ↦ f p = c)
  have hmaps : ∀ p ∈ good, f p ∈ colors := by
    intro p hp
    have hpX := hDX (Finset.mem_sdiff.mp hp).1
    have h₁ := hxA p hpX (joiningSlope ξ υ p q₀)
    have h₂ := hyB p hpX (joiningSlope ξ υ p q₀)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [f]; omega),
      Finset.mem_range.mpr (by dsimp [f]; omega)⟩
  have hcolors : colors.Nonempty := by
    obtain ⟨p, hp⟩ := hgn
    exact ⟨f p, hmaps p hp⟩
  let counts := colors.image (fun c ↦ (fiber c).card)
  have hcounts : counts.Nonempty := hcolors.image _
  obtain ⟨c, hc, hmax⟩ := Finset.mem_image.mp (counts.max'_mem hcounts)
  have hsize : good.card ≤ (V + 1)^2 * (fiber c).card := by
    calc
      _ = ∑ j ∈ colors, (fiber j).card := Finset.card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ _j ∈ colors, (fiber c).card := by
        apply Finset.sum_le_sum
        intro j hj
        rw [hmax]
        exact counts.le_max' _ (Finset.mem_image_of_mem _ hj)
      _ = _ := by simp [colors, pow_two]
  have hfiber : (fiber c).Nonempty := by
    by_contra hn
    have hc0 : (fiber c).card = 0 := Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    rw [hc0, mul_zero] at hsize
    exact (not_le_of_gt (card_pos.mpr hgn)) hsize
  refine ⟨fiber c, (Finset.filter_subset _ _).trans Finset.sdiff_subset, F, hFE, hfiber, ⟨q₀, hq₀⟩,
    ?_, hFcard, c.1, c.2, ?_⟩
  · exact hgoodCard.trans <| by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hsize
  · intro p hp q hq
    obtain ⟨hpg, hpc⟩ := Finset.mem_filter.mp hp
    have heq := (hgood p hpg q q₀ hq hq₀).trans hpc
    exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

theorem take_left [DecidableEq α] (ξ : α → ℝ) (m : ℕ) (T : Finset α) (hm : m ≤ T.card)
    (hξ : Set.InjOn ξ T) : ∃ L ⊆ T, L.card = m ∧ LeftOf ξ L (T \ L) := by
  classical
  induction m generalizing T with
  | zero => exact ⟨∅, Finset.empty_subset _, by simp, by simp [LeftOf]⟩
  | succ m ih =>
    have hT := card_pos.mp (by omega : 0 < T.card)
    let c := (T.image ξ).min' (hT.image _)
    obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp ((T.image ξ).min'_mem (hT.image ξ))
    change ξ p = c at hpc
    have hpmin (q : α) (hq : q ∈ T) : ξ p ≤ ξ q := by
      rw [hpc]
      exact (T.image ξ).min'_le _ (Finset.mem_image_of_mem _ hq)
    have herase : T.erase p ⊆ T := Finset.erase_subset _ _
    have hcard : m ≤ (T.erase p).card := by rw [Finset.card_erase_of_mem hp]; omega
    obtain ⟨L, hLe, hLc, hL⟩ := ih (T.erase p) hcard (hξ.mono herase)
    have hpL : p ∉ L := fun h ↦ Finset.notMem_erase p T (hLe h)
    refine ⟨insert p L, Finset.insert_subset_iff.mpr ⟨hp, hLe.trans herase⟩, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hpL, hLc]
    · intro a ha b hb
      obtain ⟨hbT, hbL⟩ := Finset.mem_sdiff.mp hb
      have hbp : b ≠ p := fun heq ↦ hbL (heq ▸ Finset.mem_insert_self _ _)
      rcases Finset.mem_insert.mp ha with rfl | haL
      · exact lt_of_le_of_ne (hpmin b hbT) (fun h ↦ hbp (hξ hp hbT h).symm)
      · exact hL a haL b <| Finset.mem_sdiff.mpr
          ⟨Finset.mem_erase.mpr ⟨hbp, hbT⟩, fun hb' ↦ hbL (Finset.mem_insert_of_mem hb')⟩

/-- The slope version of the half-plane property for two groups. -/
def UniformEdgeSides (ξ υ : α → ℝ) (G H : Finset α) : Prop :=
  ∀ a ∈ G, ∀ b ∈ G, ξ a < ξ b →
    (∀ q ∈ H, joiningSlope ξ υ a q < joiningSlope ξ υ a b ∧
      joiningSlope ξ υ b q < joiningSlope ξ υ a b) ∨
    (∀ q ∈ H, joiningSlope ξ υ a b < joiningSlope ξ υ a q ∧
      joiningSlope ξ υ a b < joiningSlope ξ υ b q)

/-- A uniform slope side gives an open half-plane containing the other group. -/
theorem UniformEdgeSides.halfPlane {ξ υ : α → ℝ} {G H : Finset α}
    (h : UniformEdgeSides ξ υ G H) (ho : LeftOf ξ G H ∨ LeftOf ξ H G)
    {a b : α} (ha : a ∈ G) (hb : b ∈ G) (hab : ξ a < ξ b) :
    ∃ s : Bool, ∀ q ∈ H,
      openSide s ((throughSlope ξ υ a (joiningSlope ξ υ a b)).eval (ξ q) (υ q)) := by
  rcases ho with ho | ho <;> rcases h a ha b hb hab with h | h
  · refine ⟨false, fun q hq ↦ ?_⟩
    have hξ := ho a ha q hq
    simp only [openSide, Bool.false_eq_true, if_false, throughSlope_eval _ _ _ _ _ hξ.ne']
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hξ) (sub_neg.mpr (h q hq).1)
  · refine ⟨true, fun q hq ↦ ?_⟩
    have hξ := ho a ha q hq
    simp only [openSide, if_true, throughSlope_eval _ _ _ _ _ hξ.ne']
    exact mul_pos (sub_pos.mpr hξ) (sub_pos.mpr (h q hq).1)
  · refine ⟨true, fun q hq ↦ ?_⟩
    have hξ := ho q hq a ha
    simp only [openSide, if_true, throughSlope_eval _ _ _ _ _ hξ.ne]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hξ) (sub_neg.mpr (h q hq).1)
  · refine ⟨false, fun q hq ↦ ?_⟩
    have hξ := ho q hq a ha
    simp only [openSide, Bool.false_eq_true, if_false, throughSlope_eval _ _ _ _ _ hξ.ne]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hξ) (sub_pos.mpr (h q hq).1)

/-- The outputs of the two-pass selection in Proposition 3.2. -/
structure JoiningGroups (ξ υ : α → ℝ) (x y : α → ℝ → ℕ) (T : Finset α) (V k : ℕ) where
  left : Finset α
  right : Finset α
  left_subset : left ⊆ T
  right_subset : right ⊆ T
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  ordered : LeftOf ξ left right
  left_card : T.card ≤ 12 * (V + 1)^2 * 4^k * left.card
  right_card : T.card ≤ 12 * (V + 1)^2 * 4^k * right.card
  x₁ : ℕ
  y₁ : ℕ
  x₂ : ℕ
  y₂ : ℕ
  left_rank : ∀ p ∈ left, ∀ q ∈ right,
    x p (joiningSlope ξ υ p q) = x₁ ∧ y p (joiningSlope ξ υ p q) = y₁
  right_rank : ∀ p ∈ left, ∀ q ∈ right,
    x q (joiningSlope ξ υ p q) = x₂ ∧ y q (joiningSlope ξ υ p q) = y₂
  left_edges : UniformEdgeSides ξ υ left right
  right_edges : UniformEdgeSides ξ υ right left

private theorem same_line (ξ υ : α → ℝ) (a b : α) (hab : ξ a < ξ b) (x' y' : ℝ) :
    (throughSlope ξ υ b (joiningSlope ξ υ a b)).eval x' y' =
      (throughSlope ξ υ a (joiningSlope ξ υ a b)).eval x' y' := by
  have h := throughSlope_eval ξ υ a b (joiningSlope ξ υ a b) hab.ne'
  rw [sub_self, mul_zero] at h
  simp only [LineForm.eval, throughSlope] at h ⊢
  linarith

private theorem sideOfLine_same {a b d d' : ℝ} (h : d * a = d' * b)
    (hside : (0 < d ∧ 0 < d') ∨ (d < 0 ∧ d' < 0)) :
    (0 < a ↔ 0 < b) ∧ (a < 0 ↔ b < 0) := by
  have pos (r s : ℝ) (hr : 0 < r) : (0 < r * s ↔ 0 < s) ∧ (r * s < 0 ↔ s < 0) := by
    have h₁ : r * 0 < r * s ↔ 0 < s := (strictMono_mul_left_of_pos hr).lt_iff_lt
    have h₂ : r * s < r * 0 ↔ s < 0 := (strictMono_mul_left_of_pos hr).lt_iff_lt
    simpa using And.intro h₁ h₂
  have neg (r s : ℝ) (hr : r < 0) : (r * s < 0 ↔ 0 < s) ∧ (0 < r * s ↔ s < 0) := by
    have h₁ : r * s < r * 0 ↔ 0 < s := mul_lt_mul_left_of_neg hr
    have h₂ : r * 0 < r * s ↔ s < 0 := mul_lt_mul_left_of_neg hr
    simpa using And.intro h₁ h₂
  rcases hside with hd | hd
  · have hf := pos d a hd.1
    rw [h] at hf
    exact ⟨hf.1.symm.trans (pos d' b hd.2).1, hf.2.symm.trans (pos d' b hd.2).2⟩
  · have hf := neg d a hd.1
    rw [h] at hf
    exact ⟨hf.1.symm.trans (neg d' b hd.2).1, hf.2.symm.trans (neg d' b hd.2).2⟩

private theorem uniform_of_constant (ξ υ : α → ℝ) (X G H : Finset α) (x : α → ℝ → ℕ)
    (hGX : G ⊆ X) (hHX : H ⊆ X) (hH : H.Nonempty)
    (hside : LeftOf ξ G H ∨ LeftOf ξ H G)
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ q ∈ X, ξ a < ξ b → ξ q ≠ ξ a → ξ q ≠ ξ b →
      joiningSlope ξ υ a q ≠ joiningSlope ξ υ a b)
    (hmono : ∀ p ∈ X, Antitone (x p))
    (hext : ∀ a ∈ X, ∀ b ∈ X, ξ a < ξ b →
      x a (joiningSlope ξ υ a b) < x b (joiningSlope ξ υ a b))
    (c : ℕ) (hconst : ∀ p ∈ G, ∀ q ∈ H, x p (joiningSlope ξ υ p q) = c) :
    UniformEdgeSides ξ υ G H := by
  intro a ha b hb hab
  let t := joiningSlope ξ υ a b
  let sa (q : α) := joiningSlope ξ υ a q - t
  let sb (q : α) := joiningSlope ξ υ b q - t
  have signs (q : α) (hq : q ∈ H) :
      (0 < ξ q - ξ a ∧ 0 < ξ q - ξ b) ∨ (ξ q - ξ a < 0 ∧ ξ q - ξ b < 0) := by
    rcases hside with h | h
    · exact Or.inl ⟨sub_pos.mpr (h a ha q hq), sub_pos.mpr (h b hb q hq)⟩
    · exact Or.inr ⟨sub_neg.mpr (h q hq a ha), sub_neg.mpr (h q hq b hb)⟩
  have nonzero (q : α) (hq : q ∈ H) : ξ q ≠ ξ a ∧ ξ q ≠ ξ b := by
    rcases signs q hq with h | h
    · exact ⟨sub_ne_zero.mp h.1.ne', sub_ne_zero.mp h.2.ne'⟩
    · exact ⟨sub_ne_zero.mp h.1.ne, sub_ne_zero.mp h.2.ne⟩
  have hsign (q : α) (hq : q ∈ H) : (0 < sa q ↔ 0 < sb q) ∧ (sa q < 0 ↔ sb q < 0) := by
    obtain ⟨hqa, hqb⟩ := nonzero q hq
    have hsame := same_line ξ υ a b hab (ξ q) (υ q)
    change (throughSlope ξ υ b t).eval (ξ q) (υ q) =
      (throughSlope ξ υ a t).eval (ξ q) (υ q) at hsame
    rw [throughSlope_eval _ _ _ _ _ hqa, throughSlope_eval _ _ _ _ _ hqb] at hsame
    exact sideOfLine_same hsame.symm (signs q hq)
  have hne (q : α) (hq : q ∈ H) : sa q ≠ 0 :=
    sub_ne_zero.mpr (hgen a (hGX ha) b (hGX hb) q (hHX hq) hab (nonzero q hq).1 (nonzero q hq).2)
  have hs c₁ (hc₁ : c₁ ∈ G) {p q : α} (hp : p ∈ H) (hq : q ∈ H)
      (hle : joiningSlope ξ υ c₁ p ≤ t) (hge : t ≤ joiningSlope ξ υ c₁ q) : x c₁ t = c := by
    have h₁ := hmono c₁ (hGX hc₁) hle
    have h₂ := hmono c₁ (hGX hc₁) hge
    rw [hconst c₁ hc₁ p hp] at h₁
    rw [hconst c₁ hc₁ q hq] at h₂
    exact le_antisymm h₁ h₂
  have hn (p q : α) (hp : p ∈ H) (hq : q ∈ H) (hpa : sa p < 0) (hqa : 0 < sa q) : False := by
    have hpb := (hsign p hp).2.mp hpa
    have hqb := (hsign q hq).1.mp hqa
    have ea := hs a ha hp hq (sub_neg.mp hpa).le (sub_pos.mp hqa).le
    have eb := hs b hb hp hq (sub_neg.mp hpb).le (sub_pos.mp hqb).le
    have hlt : x a t < x b t := hext a (hGX ha) b (hGX hb) hab
    omega
  obtain ⟨p, hp⟩ := hH
  rcases lt_or_gt_of_ne (hne p hp) with hpa | hpa
  · left
    intro q hq
    have hqa : sa q < 0 := by
      rcases lt_or_gt_of_ne (hne q hq) with h | h
      · exact h
      · exact False.elim (hn p q hp hq hpa h)
    exact ⟨sub_neg.mp hqa, sub_neg.mp ((hsign q hq).2.mp hqa)⟩
  · right
    intro q hq
    have hqa : 0 < sa q := by
      rcases lt_or_gt_of_ne (hne q hq) with h | h
      · exact False.elim (hn q p hq hp h hpa)
      · exact h
    exact ⟨sub_pos.mp hqa, sub_pos.mp ((hsign q hq).1.mp hqa)⟩

/-- Proposition 3.2. The choice of `k` is expressed by its equivalent integer
inequality, which controls the number of crossings after the equipartitions. -/
theorem proposition32 (ξ υ : α → ℝ) (X T : Finset α) (x y : α → ℝ → ℕ)
    (A B V k : ℕ) (hTX : T ⊆ X) (hT : 2 ≤ T.card)
    (hinj : Set.InjOn ξ X)
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ q ∈ X, ξ a < ξ b → ξ q ≠ ξ a → ξ q ≠ ξ b →
      joiningSlope ξ υ a q ≠ joiningSlope ξ υ a b)
    (hx : ∀ p ∈ X, Antitone (x p)) (hy : ∀ p ∈ X, Monotone (y p))
    (hxA : ∀ p ∈ X, ∀ t, x p t ≤ A) (hyB : ∀ p ∈ X, ∀ t, y p t ≤ B)
    (hAB : A + B ≤ V)
    (hext : ∀ a ∈ X, ∀ b ∈ X, ξ a < ξ b →
      x a (joiningSlope ξ υ a b) < x b (joiningSlope ξ υ a b))
    (hequip : TwoLineEquipartition ξ υ X) (hk : 2 * V * 3 ^ k ≤ 4 ^ k) :
    Nonempty (JoiningGroups ξ υ x y T V k) := by
  classical
  obtain ⟨L, hLT, hLcard, hLR⟩ := take_left ξ (T.card / 2) T (by omega) (hinj.mono hTX)
  let R := T \ L
  have hRT : R ⊆ T := Finset.sdiff_subset
  have hRcard : R.card + L.card = T.card := Finset.card_sdiff_add_card_eq_card hLT
  have hLn : L.Nonempty := card_pos.mp (by omega)
  have hRn : R.Nonempty := card_pos.mp (by omega)
  obtain ⟨D₁, hD₁L, E₁, hE₁R, hD₁, hE₁, hD₁c, hE₁c, x₁, y₁, hr₁⟩ :=
    oneDirection ξ υ X L R x y A B V k hx hy hxA hyB hAB (hLT.trans hTX) (hRT.trans hTX)
      hLn hRn (Or.inl hLR) hequip hk
  obtain ⟨D₂, hD₂E₁, E₂, hE₂D₁, hD₂, hE₂, hD₂c, hE₂c, x₂, y₂, hr₂⟩ :=
    oneDirection ξ υ X E₁ D₁ x y A B V k hx hy hxA hyB hAB ((hE₁R.trans hRT).trans hTX)
      ((hD₁L.trans hLT).trans hTX) hE₁ hD₁ (Or.inr (hLR.mono hD₁L hE₁R)) hequip hk
  have hE₂T := hE₂D₁.trans (hD₁L.trans hLT)
  have hD₂T := hD₂E₁.trans (hE₁R.trans hRT)
  have hE₂D₂ := hLR.mono (hE₂D₁.trans hD₁L) (hD₂E₁.trans hE₁R)
  have hE₂r p (hp : p ∈ E₂) q (hq : q ∈ D₂) := hr₁ p (hE₂D₁ hp) q (hD₂E₁ hq)
  have hD₂r q (hq : q ∈ D₂) p (hp : p ∈ E₂) := hr₂ q hq p hp
  refine ⟨⟨E₂, D₂, hE₂T, hD₂T, hE₂, hD₂, hE₂D₂, ?_, ?_, x₁, y₁, x₂, y₂,
    hE₂r, ?_, ?_, ?_⟩⟩
  · calc
      T.card ≤ 3 * L.card := by omega
      _ ≤ 3 * (2 * (V + 1)^2 * D₁.card) := Nat.mul_le_mul_left _ hD₁c
      _ ≤ 3 * (2 * (V + 1)^2 * (2 * 4^k * E₂.card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hE₂c)
      _ = _ := by ring
  · calc
      T.card ≤ 3 * R.card := by omega
      _ ≤ 3 * (2 * 4^k * E₁.card) := Nat.mul_le_mul_left _ hE₁c
      _ ≤ 3 * (2 * 4^k * (2 * (V + 1)^2 * D₂.card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hD₂c)
      _ = _ := by ring
  · intro p hp q hq
    rw [joiningSlope_comm ξ υ p q]
    exact hD₂r q hq p hp
  · exact uniform_of_constant ξ υ X E₂ D₂ x (hE₂T.trans hTX) (hD₂T.trans hTX)
      hD₂ (Or.inl hE₂D₂) hgen hx hext x₁ (fun p hp q hq ↦ (hE₂r p hp q hq).1)
  · exact uniform_of_constant ξ υ X D₂ E₂ x (hD₂T.trans hTX) (hE₂T.trans hTX)
      hE₂ (Or.inr hE₂D₂) hgen hx hext x₂ (fun q hq p hp ↦ (hD₂r q hq p hp).1)

/-- The number of equipartition rounds used in Proposition 3.2. -/
def partitionRounds (V : ℕ) : ℕ := ⌈Real.logb (4 / 3) (2 * (V : ℝ))⌉₊

theorem partitionRounds_spec {V : ℕ} (hV : 1 ≤ V) :
    2 * V * 3 ^ partitionRounds V ≤ 4 ^ partitionRounds V := by
  have hv : 0 < (2 : ℝ) * V := by positivity
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 4 / 3) hv).mp
    (Nat.le_ceil (Real.logb (4 / 3) (2 * (V : ℝ))))
  change (2 : ℝ) * V ≤ (4 / 3 : ℝ) ^ (partitionRounds V : ℝ) at h
  rw [Real.rpow_natCast, div_pow] at h
  have h' := (le_div_iff₀ (by positivity : (0 : ℝ) < 3 ^ partitionRounds V)).mp h
  exact_mod_cast h'

theorem partitionRounds_le {V : ℕ} (hV : 1 ≤ V) :
    (partitionRounds V : ℝ) ≤ 1 + 3 * Real.logb 2 (2 * (V : ℝ)) := by
  have hV' : 1 ≤ (V : ℝ) := by exact_mod_cast hV
  have hb : (1 : ℝ) < 4 / 3 := by norm_num
  have h₁ : (1 : ℝ) ≤ 2 * (V : ℝ) := by linarith
  have h₂ : 0 < (2 : ℝ) * V := by linarith
  have h3 : (2 : ℝ) ≤ (4 / 3 : ℝ) ^ (3 : ℕ) := by norm_num
  have hlog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) h₁
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) h3 hlog
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) h₂] at hpow
  have hpow' : (2 : ℝ) * V ≤ (4 / 3 : ℝ) ^ (3 * Real.logb 2 (2 * (V : ℝ))) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4 / 3), Real.rpow_ofNat]
    exact hpow
  have hlog' := (Real.logb_le_iff_le_rpow hb h₂).mpr hpow'
  have hc := Nat.ceil_lt_add_one (Real.logb_nonneg hb h₁)
  change (partitionRounds V : ℝ) < Real.logb (4 / 3) (2 * (V : ℝ)) + 1 at hc
  linarith

/-- The loss bound used in Section 7, with the same coefficient as in the paper. -/
theorem joining_log_loss {V : ℕ} (hV : 2 ≤ V) :
    Real.logb 2 (24 * ((V : ℝ) + 1)^2 * 4^partitionRounds V) ≤
      15 * Real.logb 2 ((V : ℝ) + 2) := by
  have hV' : 2 ≤ (V : ℝ) := by exact_mod_cast hV
  have hne : (V : ℝ) ≠ 0 := by positivity
  have hV1 : 0 < (V : ℝ) + 1 := by positivity
  have hb : (1 : ℝ) < 2 := by norm_num
  have h₁ := Real.logb_le_logb_of_le hb hV1 (show (V : ℝ) + 1 ≤ V + 2 by linarith)
  have h₂ := Real.logb_le_logb_of_le hb (show (0 : ℝ) < V by positivity)
    (show (V : ℝ) ≤ V + 2 by linarith)
  have h_24 := Real.logb_le_logb_of_le hb (by norm_num : (0 : ℝ) < 24)
    (by norm_num : (24 : ℝ) ≤ (2 : ℝ) ^ (5 : ℕ))
  have h_4 := Real.logb_le_logb_of_le hb (by norm_num : (0 : ℝ) < (2 : ℝ)^2)
    (show (2 : ℝ) ^ (2 : ℕ) ≤ V + 2 by norm_num; linarith)
  have hself : Real.logb 2 2 = 1 := Real.logb_self_eq_one hb
  rw [Real.logb_pow, hself, mul_one] at h_24 h_4
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ)^2 by norm_num, Real.logb_pow, hself]
    norm_num
  have hk := partitionRounds_le (show 1 ≤ V by omega)
  rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hne, hself] at hk
  rw [Real.logb_mul (by positivity : (24 : ℝ) * ((V : ℝ) + 1)^2 ≠ 0)
      (by positivity : (4 : ℝ)^partitionRounds V ≠ 0),
    Real.logb_mul (by norm_num : (24 : ℝ) ≠ 0) (by positivity : ((V : ℝ) + 1)^2 ≠ 0),
    Real.logb_pow, Real.logb_pow, h4]
  norm_num at h_24 h_4 ⊢
  linarith

/-- The group sizes of Proposition 3.2 in the logarithmic form used in Section 7. -/
theorem joining_group_log_loss {V n m : ℕ} (hV : 2 ≤ V) (hn : 0 < n) (hm : 0 < m)
    (hcard : n ≤ 12 * (V + 1)^2 * 4^partitionRounds V * m) :
    Real.logb 2 (2 * (n : ℝ) / m) ≤ 15 * Real.logb 2 ((V : ℝ) + 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hcast : (n : ℝ) ≤ 12 * ((V : ℝ) + 1)^2 * 4^partitionRounds V * m := by
    exact_mod_cast hcard
  have hratio : (2 : ℝ) * n / m ≤ 24 * ((V : ℝ) + 1)^2 * 4^partitionRounds V := by
    apply (div_le_iff₀ hm').mpr
    linarith only [hcast]
  exact (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hratio).trans
    (joining_log_loss hV)

end

end ESVerify
