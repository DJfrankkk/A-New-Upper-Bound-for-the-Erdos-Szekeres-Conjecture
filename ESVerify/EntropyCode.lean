import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic

namespace ESVerify

/-- The shape of a dyadic subdivision, with a signed height increment at each leaf. -/
inductive EntropyTree where
  | leaf (z : ℤ)
  | branch (left right : EntropyTree)

namespace EntropyTree

/-- Number of intervals in the subdivision. -/
def leaves : EntropyTree → ℕ
  | .leaf _ => 1
  | .branch l r => l.leaves + r.leaves

/-- Sum of the magnitudes of the coded height increments. -/
def jumpMass : EntropyTree → ℕ
  | .leaf z => z.natAbs
  | .branch l r => l.jumpMass + r.jumpMass

private def code : EntropyTree → List (Fin 5)
  | .leaf z => (if z < 0 then 0 else 1) :: (List.replicate z.natAbs 2 ++ [3])
  | .branch l r => 4 :: (l.code ++ r.code)

private theorem code_length (t : EntropyTree) :
    t.code.length + 1 = 3 * t.leaves + t.jumpMass := by
  induction t with
  | leaf z =>
    simp only [code, leaves, jumpMass, List.length_cons, List.length_append,
      List.length_replicate, List.length_nil]
    omega
  | branch l r hl hr =>
    simp only [code, leaves, jumpMass, List.length_cons, List.length_append]
    omega

private theorem unary_prefix {n m : ℕ} {a b : List (Fin 5)}
    (h : List.replicate n 2 ++ 3 :: a = List.replicate m 2 ++ 3 :: b) :
    n = m ∧ a = b := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa using h
    | succ m => simp [List.replicate_succ] at h
  | succ n ih =>
    cases m with
    | zero => simp [List.replicate_succ] at h
    | succ m =>
      obtain ⟨hnm, hab⟩ := ih (by simpa [List.replicate_succ] using h)
      exact ⟨congrArg Nat.succ hnm, hab⟩

private theorem code_prefix (t u : EntropyTree) (a b : List (Fin 5)) :
    t.code ++ a = u.code ++ b → t = u ∧ a = b := by
  induction t generalizing u a b with
  | leaf z =>
    intro h
    cases u with
    | leaf w =>
      have hh : (if z < 0 then (0 : Fin 5) else 1) = (if w < 0 then 0 else 1) ∧
          List.replicate z.natAbs (2 : Fin 5) ++ 3 :: a =
            List.replicate w.natAbs 2 ++ 3 :: b := List.cons.inj
        (by simpa only [code, List.cons_append, List.append_assoc, List.nil_append] using h)
      obtain ⟨habs, rfl⟩ := unary_prefix hh.2
      have hsame : z < 0 ↔ w < 0 := by
        constructor
        · intro hz
          by_contra hw
          have hbad : (0 : Fin 5) = 1 := by simpa only [if_pos hz, if_neg hw] using hh.1
          exact (by decide : (0 : Fin 5) ≠ 1) hbad
        · intro hw
          by_contra hz
          have hbad : (1 : Fin 5) = 0 := by simpa only [if_neg hz, if_pos hw] using hh.1
          exact (by decide : (1 : Fin 5) ≠ 0) hbad
      have hzeq : z = w := by
        rcases Int.natAbs_eq_natAbs_iff.mp habs with hEq | hOpp
        · exact hEq
        · by_cases hz : z < 0
          · have hw := hsame.mp hz
            omega
          · have hw : ¬ w < 0 := fun hw => hz (hsame.mpr hw)
            omega
      exact ⟨congrArg EntropyTree.leaf hzeq, rfl⟩
    | branch l r =>
      have htag : (if z < 0 then (0 : Fin 5) else 1) = 4 :=
        (List.cons.inj (by simpa only [code, List.cons_append] using h)).1
      split at htag
      · exact ((by decide : (0 : Fin 5) ≠ 4) htag).elim
      · exact ((by decide : (1 : Fin 5) ≠ 4) htag).elim
  | branch l r hl hr =>
    intro h
    cases u with
    | leaf z =>
      have htag : (4 : Fin 5) = if z < 0 then 0 else 1 :=
        (List.cons.inj (by simpa only [code, List.cons_append] using h)).1
      split at htag
      · exact ((by decide : (4 : Fin 5) ≠ 0) htag).elim
      · exact ((by decide : (4 : Fin 5) ≠ 1) htag).elim
    | branch l' r' =>
      have hh : l.code ++ (r.code ++ a) = l'.code ++ (r'.code ++ b) := by
        simpa only [code, List.cons_append, List.cons.injEq, true_and, List.append_assoc] using h
      obtain ⟨rfl, hr'⟩ := hl l' _ _ hh
      obtain ⟨rfl, rfl⟩ := hr r' _ _ hr'
      exact ⟨rfl, rfl⟩

private def padded (L : ℕ) (t : EntropyTree) (i : Fin L) : Option (Fin 5) :=
  t.code[i.val]?

private theorem padded_inj {L : ℕ} {t u : EntropyTree}
    (ht : 3 * t.leaves + t.jumpMass ≤ L) (hu : 3 * u.leaves + u.jumpMass ≤ L)
    (heq : padded L t = padded L u) : t = u := by
  have hc : t.code = u.code := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < L
    · exact congrFun heq ⟨j, hj⟩
    · have ht' := code_length t
      have hu' := code_length u
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  exact (code_prefix t u [] [] (by simpa using hc)).1

end EntropyTree

/-- A family of 6^L codes contains every dyadic tree with total encoding cost at most L. -/
theorem entropyTreeCover (L : ℕ) :
    ∃ (M : ℕ) (trees : Fin M → EntropyTree), M = 6 ^ L ∧
      ∀ t : EntropyTree, 3 * t.leaves + t.jumpMass ≤ L → ∃ m, trees m = t := by
  classical
  let e := Fintype.equivFin (Fin L → Option (Fin 5))
  let decode (f : Fin L → Option (Fin 5)) : EntropyTree :=
    if he : ∃ t : EntropyTree, 3 * t.leaves + t.jumpMass ≤ L ∧ EntropyTree.padded L t = f then
      Classical.choose he
    else
      .leaf 0
  refine ⟨Fintype.card (Fin L → Option (Fin 5)), fun m => decode (e.symm m), ?_, ?_⟩
  · simp
  · intro t ht
    refine ⟨e (EntropyTree.padded L t), ?_⟩
    change decode (e.symm (e (EntropyTree.padded L t))) = t
    rw [Equiv.symm_apply_apply]
    have he : ∃ u : EntropyTree, 3 * u.leaves + u.jumpMass ≤ L ∧
        EntropyTree.padded L u = EntropyTree.padded L t := ⟨t, ht, rfl⟩
    dsimp only [decode]
    rw [dif_pos he]
    exact EntropyTree.padded_inj (Classical.choose_spec he).1 ht (Classical.choose_spec he).2

end ESVerify
