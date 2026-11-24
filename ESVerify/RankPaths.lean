import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-! The rank-path encoding of Proposition 2.3. A word is represented by its
positive positions. The construction places each right step just after all the
down steps that must precede it. -/

set_option autoImplicit false

namespace ESVerify

namespace RankPath

/-- Number of right steps taken strictly before time \(k\). -/
def prefixCard {N : ℕ} (w : Finset (Fin N)) (k : ℕ) : ℕ :=
  (w.filter fun i => i.val < k).card

/-- Sum of the signs at time \(k\), for \(k\) at most the length of the word. -/
def height {N : ℕ} (w : Finset (Fin N)) (k : ℕ) : ℤ :=
  2 * (prefixCard w k : ℤ) - (k : ℤ)

def time (B x y : ℕ) : ℕ := x + (B - y)

theorem prefixCard_mono {N : ℕ} (w : Finset (Fin N)) : Monotone (prefixCard w) := by
  intro i j hij
  apply Finset.card_le_card
  intro a ha
  obtain ⟨haw, hai⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨haw, hai.trans_le hij⟩

theorem prefixCard_le_add {N : ℕ} (w : Finset (Fin N)) {i j : ℕ} (hij : i ≤ j) :
    prefixCard w j ≤ prefixCard w i + (j - i) := by
  classical
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have step : prefixCard w (j + 1) ≤ prefixCard w j + 1 := by
      by_cases hj : j < N
      · let p : Fin N := ⟨j, hj⟩
        have hincl : (w.filter fun a => a.val < j + 1) ⊆
            insert p (w.filter fun a => a.val < j) := by
          intro a ha
          obtain ⟨haw, hlt⟩ := Finset.mem_filter.mp ha
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨haw, h⟩)
          · have hap : a = p := Fin.ext h
            rw [hap]
            exact Finset.mem_insert_self _ _
        exact (Finset.card_le_card hincl).trans (Finset.card_insert_le _ _)
      · have heq : (w.filter fun a => a.val < j + 1) =
            w.filter (fun a => a.val < j) := by
          apply Finset.filter_congr
          intro a _
          have ha : a.val < j := a.isLt.trans_le (Nat.le_of_not_gt hj)
          exact iff_of_true (ha.trans (Nat.lt_succ_self _)) ha
        unfold prefixCard
        rw [heq]
        omega
    omega

theorem prefixCard_univ {N k : ℕ} (hk : k ≤ N) :
    prefixCard (Finset.univ : Finset (Fin N)) k = k := by
  unfold prefixCard
  have hc : (Finset.univ.filter fun i : Fin N => i.val < k).card =
      (Finset.range (k)).card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro i hi
      have hix := Finset.mem_range.mp hi
      exact ⟨⟨i, hix.trans_le hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hix⟩, rfl⟩
  rwa [Finset.card_range] at hc

section Construction

variable {ι : Type*}

private noncomputable def preceding (B : ℕ) (x y : ι → ℕ) (i : ℕ) : ℕ := by
  classical
  exact ((Finset.range (B + 1)).filter fun b => ∃ t, x t ≤ i ∧ b = B - y t).sup id

private theorem preceding_le (B : ℕ) (x y : ι → ℕ) (i c : ℕ)
    (hc : ∀ t, x t ≤ i → B - y t ≤ c) : preceding B x y i ≤ c := by
  classical
  unfold preceding
  apply Finset.sup_le
  intro b hb
  obtain ⟨t, ht, rfl⟩ := (Finset.mem_filter.mp hb).2
  exact hc t ht

private theorem le_preceding (B : ℕ) (x y : ι → ℕ) (i : ℕ) (t : ι)
    (ht : x t ≤ i) : B - y t ≤ preceding B x y i := by
  classical
  unfold preceding
  apply Finset.le_sup (f := id)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)), t, ht, rfl⟩

private theorem preceding_mono (B : ℕ) (x y : ι → ℕ) :
    Monotone (preceding B x y) :=
  fun i j hij => preceding_le B x y i _ fun t ht => le_preceding B x y j t (ht.trans hij)

private noncomputable def rightPosition (A B : ℕ) (x y : ι → ℕ) :
    Fin A ↪ Fin (A + B) where
  toFun i := ⟨i.val + preceding B x y i.val, by
    have hi := i.isLt
    have hB := preceding_le B x y i.val B fun t _ => Nat.sub_le _ _
    omega⟩
  inj' := by
    intro i j h
    have hval := congrArg Fin.val h
    change i.val + preceding B x y i.val = j.val + preceding B x y j.val at hval
    apply Fin.ext
    rcases le_total i.val j.val with hij | hji
    · have := preceding_mono B x y hij
      omega
    · have := preceding_mono B x y hji
      omega

/-- The set of positions at which the path takes a right step. -/
noncomputable def positivePositions (A B : ℕ) (x y : ι → ℕ) : Finset (Fin (A + B)) :=
  Finset.univ.map (rightPosition A B x y)

@[simp] theorem card_positivePositions (A B : ℕ) (x y : ι → ℕ) :
    (positivePositions A B x y).card = A := by
  simp [positivePositions]

variable [LinearOrder ι]

private theorem position_lt_time_iff (A B : ℕ) (x y : ι → ℕ)
    (hx : Antitone x) (hy : Monotone y) (t : ι) (i : Fin A) :
    (rightPosition A B x y i).val < time B (x t) (y t) ↔ i.val < x t := by
  change i.val + preceding B x y i.val < x t + (B - y t) ↔ i.val < x t
  constructor
  · intro h
    by_contra! hi
    have hb := le_preceding B x y i.val t hi
    omega
  · intro hi
    have h := preceding_le B x y i.val (B - y t) (by
      intro t' ht'
      have htt' : t ≤ t' := by
        by_contra! h
        exact (not_lt_of_ge (hx h.le)) (ht'.trans_lt hi)
      exact Nat.sub_le_sub_left (hy htt') B)
    omega

theorem prefixCard_at_time (A B : ℕ) (x y : ι → ℕ) (hx : Antitone x) (hy : Monotone y)
    (t : ι) (hxA : x t ≤ A) :
    prefixCard (positivePositions A B x y) (time B (x t) (y t)) = x t := by
  unfold prefixCard positivePositions
  rw [Finset.filter_map, Finset.card_map]
  have hf :
      (Finset.univ.filter fun i : Fin A =>
          (rightPosition A B x y i).val < time B (x t) (y t)) =
      Finset.univ.filter (fun i : Fin A => i.val < x t) := by
    apply Finset.filter_congr
    intro i _
    exact position_lt_time_iff A B x y hx hy t i
  change (Finset.univ.filter fun i : Fin A =>
    (rightPosition A B x y i).val < time B (x t) (y t)).card = x t
  rw [hf]
  exact prefixCard_univ hxA

theorem height_at_time (A B : ℕ) (x y : ι → ℕ) (hx : Antitone x) (hy : Monotone y)
    (t : ι) (hxA : x t ≤ A) (hyB : y t ≤ B) :
    height (positivePositions A B x y) (time B (x t) (y t)) =
      (x t : ℤ) + (y t : ℤ) - B := by
  rw [height, prefixCard_at_time A B x y hx hy t hxA, time, Nat.cast_add,
    Nat.cast_sub hyB]
  omega

end Construction

theorem unequal_of_increasing_ranks {N B xp yp xq yq : ℕ}
    {wp wq : Finset (Fin N)} (hp : prefixCard wp (time B xp yp) = xp)
    (hq : prefixCard wq (time B xq yq) = xq)
    (hyp : yp ≤ B) (hyq : yq ≤ B) (hx : xp < xq) (hy : yp < yq) : wp ≠ wq := by
  intro heq
  subst wq
  rcases le_total (time B xp yp) (time B xq yq) with h | h
  · have hh := prefixCard_le_add wp h
    rw [hp, hq] at hh
    unfold time at *
    omega
  · have hh := prefixCard_mono wp h
    rw [hp, hq] at hh
    omega

end RankPath

/-- Proposition 2.3, starting from the two ending rank functions and their
extension inequalities. The positive-position sets are sign words with \(A\)
positive and \(B\) negative steps. -/
theorem rankPaths {α ι : Type*} [LinearOrder ι] (A B : ℕ)
    (cap cup : α → ι → ℕ) (slope : α → α → ι) (leftOf : α → α → Prop)
    (side : ∀ p q, p ≠ q → leftOf p q ∨ leftOf q p)
    (cap_le : ∀ p t, cap p t ≤ A) (cup_le : ∀ p t, cup p t ≤ B)
    (cap_anti : ∀ p, Antitone (cap p)) (cup_mono : ∀ p, Monotone (cup p))
    (extension : ∀ p q, leftOf p q →
      cap p (slope p q) < cap q (slope p q) ∧ cup p (slope p q) < cup q (slope p q)) :
    ∃ w : α → Finset (Fin (A + B)), Function.Injective w ∧
      (∀ p, (w p).card = A) ∧
      (∀ p t, RankPath.time B (cap p t) (cup p t) ≤ A + B) ∧
      (∀ p t, RankPath.height (w p) (RankPath.time B (cap p t) (cup p t)) =
        (cap p t : ℤ) + (cup p t : ℤ) - B) := by
  let w (p : α) := RankPath.positivePositions A B (cap p) (cup p)
  have hsep (p q : α) (hpq : leftOf p q) : w p ≠ w q := by
    let t := slope p q
    obtain ⟨hc, hu⟩ := extension p q hpq
    exact RankPath.unequal_of_increasing_ranks
      (RankPath.prefixCard_at_time A B (cap p) (cup p) (cap_anti p) (cup_mono p) t (cap_le p t))
      (RankPath.prefixCard_at_time A B (cap q) (cup q) (cap_anti q) (cup_mono q) t (cap_le q t))
      (cup_le p t) (cup_le q t) hc hu
  refine ⟨w, ?_, fun p => RankPath.card_positivePositions A B (cap p) (cup p), ?_, ?_⟩
  · intro p q hpq
    by_contra h
    exact (side p q h).elim (fun h => hsep p q h hpq) (fun h => hsep q p h hpq.symm)
  · intro p t
    exact Nat.add_le_add (cap_le p t) (Nat.sub_le _ _)
  · intro p t
    exact RankPath.height_at_time A B (cap p) (cup p) (cap_anti p) (cup_mono p)
      t (cap_le p t) (cup_le p t)

/-- Count paths with exactly \(A\) right steps, as in the last line of
Proposition 2.3. -/
theorem card_le_choose_of_rankPaths {α : Type*} [Fintype α] (A B : ℕ)
    (w : α → Finset (Fin (A + B))) (hw : Function.Injective w)
    (hcard : ∀ p, (w p).card = A) :
    Fintype.card α ≤ (A + B).choose A := by
  classical
  have hMaps : Set.MapsTo w (Finset.univ : Finset α)
      ((Finset.univ : Finset (Fin (A + B))).powersetCard A) := by
    intro p _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard p⟩
  have h := Finset.card_le_card_of_injOn w hMaps hw.injOn
  simpa [Finset.card_powersetCard] using h

theorem card_le_pow_of_rankPaths {α : Type*} [Fintype α] (A B : ℕ)
    (w : α → Finset (Fin (A + B))) (hw : Function.Injective w)
    (hcard : ∀ p, (w p).card = A) :
    Fintype.card α ≤ 2 ^ (A + B) :=
  (card_le_choose_of_rankPaths A B w hw hcard).trans (Nat.choose_le_two_pow (A + B) A)

/-- Strict separation of the two ranks implies the height gap (3). -/
theorem rank_gap_gt_time_distance {B xp yp xq yq : ℕ}
    (hp : yp ≤ B) (hq : yq ≤ B) (hx : xp < xq) (hy : yp < yq) :
    |(RankPath.time B xq yq : ℤ) - (RankPath.time B xp yp : ℤ)| <
      (xq : ℤ) + yq - ((xp : ℤ) + yp) := by
  unfold RankPath.time
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hq, Nat.cast_sub hp, abs_lt]
  omega

end ESVerify

