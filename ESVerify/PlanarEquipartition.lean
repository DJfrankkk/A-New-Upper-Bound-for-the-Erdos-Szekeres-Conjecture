import ESVerify.Planar
import ESVerify.JoiningRanks

set_option autoImplicit false

namespace ESVerify

/-- Convert an explicit vertical cut and a second affine cut to the four
open quadrants used in the rank-selection argument. -/
theorem twoLineEquipartition_of_cuts
    (cuts : ∀ {E : Finset Point}, GeneralPosition E → DistinctAbscissae E →
      ∀ b : ℕ, 0 < b → E.card = 4 * b → ∃ a t z : ℝ,
      let L := E.filter fun p => p.1 < a
      let R := E.filter fun p => a < p.1
      (L.filter fun p => t * p.1 + p.2 < z).card = b ∧
      (L.filter fun p => z < t * p.1 + p.2).card = b ∧
      (R.filter fun p => t * p.1 + p.2 < z).card = b ∧
      (R.filter fun p => z < t * p.1 + p.2).card = b)
    {X : Finset Point} (hg : GeneralPosition X) (hx : DistinctAbscissae X) :
    TwoLineEquipartition Prod.fst Prod.snd X := by
  classical
  intro E hEX b hb hcard
  have hgE : GeneralPosition E := fun p hp q hq r hr ↦ hg p (hEX hp) q (hEX hq) r (hEX hr)
  have hxE : DistinctAbscissae E := fun _ hp _ hq ↦ hx (hEX hp) (hEX hq)
  obtain ⟨a, t, z, hL₁, hL₂, hR₁, hR₂⟩ := cuts hgE hxE b hb hcard
  let l₁ : LineForm := ⟨1, 0, -a⟩
  let l₂ : LineForm := ⟨t, 1, -z⟩
  have e₁ (p : Point) : l₁.eval p.1 p.2 = p.1 - a := by simp [l₁, LineForm.eval, sub_eq_add_neg]
  have e₂ (p : Point) : l₂.eval p.1 p.2 = t * p.1 + p.2 - z := by simp [l₂, LineForm.eval, sub_eq_add_neg]
  have hq (s : Bool × Bool) : lineQuadrant Prod.fst Prod.snd E l₁ l₂ s =
      ((E.filter fun p ↦ if s.1 then a < p.1 else p.1 < a).filter
        fun p ↦ if s.2 then z < t * p.1 + p.2 else t * p.1 + p.2 < z) := by
    ext p
    rcases s with ⟨s₁, s₂⟩
    cases s₁ <;> cases s₂ <;>
      simp [lineQuadrant, openSide, e₁, e₂, and_assoc, sub_pos, sub_neg]
  refine ⟨l₁, l₂, ?_, ?_⟩
  · simp [LineForm.independent, l₁, l₂]
  · intro s
    rw [hq]
    rcases s with ⟨s₁, s₂⟩
    cases s₁ <;> cases s₂
    · exact hL₁
    · exact hL₂
    · exact hR₁
    · exact hR₂

end ESVerify
