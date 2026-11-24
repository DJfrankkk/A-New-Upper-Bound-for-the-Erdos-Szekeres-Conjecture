import ESVerify.Planar

/-! An invertible shear puts a finite planar set in distinct horizontal coordinates. -/

set_option autoImplicit false

noncomputable section

namespace ESVerify

private def shear (t : ℝ) : Point ≃ₗ[ℝ] Point where
  toFun p := (p.1 + t * p.2, p.2)
  invFun p := (p.1 - t * p.2, p.2)
  left_inv := by intro p; ext <;> simp
  right_inv := by intro p; ext <;> simp
  map_add' := by
    intro p q
    apply Prod.ext
    · change (p.1 + q.1) + t * (p.2 + q.2) = (p.1 + t * p.2) + (q.1 + t * q.2)
      ring
    · rfl
  map_smul' := by
    intro r p
    apply Prod.ext
    · change r * p.1 + t * (r * p.2) = r * (p.1 + t * p.2)
      ring
    · rfl

private theorem shear_orientation (t : ℝ) (p q r : Point) :
    orientation (shear t p) (shear t q) (shear t r) = orientation p q r := by
  change (q.1 + t * q.2 - (p.1 + t * p.2)) * (r.2 - p.2) -
    (q.2 - p.2) * (r.1 + t * r.2 - (p.1 + t * p.2)) = _
  unfold orientation
  ring

private theorem image_convexPosition_iff (f : Point ≃ₗ[ℝ] Point) (S : Finset Point) :
    ConvexPosition (S.image f) ↔ ConvexPosition S := by
  classical
  have himage : ∀ p : Point, ((S.image f : Finset Point) : Set Point) \ {f p} =
      f '' ((S : Set Point) \ {p}) := by
    intro p
    ext w
    simp only [Finset.coe_image, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, hne⟩
      exact ⟨r, ⟨hr, fun h => hne (congrArg f h)⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hne⟩, rfl⟩
      exact ⟨⟨r, hr, rfl⟩, fun h => hne (f.injective h)⟩
  have hull : ∀ p : Point,
      f p ∈ convexHull ℝ (((S.image f : Finset Point) : Set Point) \ {f p}) ↔
        p ∈ convexHull ℝ ((S : Set Point) \ {p}) := by
    intro p
    rw [himage]
    change f p ∈ convexHull ℝ (f.toLinearMap '' ((S : Set Point) \ {p})) ↔ _
    rw [← f.toLinearMap.image_convexHull]
    exact f.injective.mem_set_image
  constructor
  · intro hf p hp
    exact fun hp' => hf (f p) (Finset.mem_image_of_mem f hp) ((hull p).2 hp')
  · intro hf w hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    exact fun hp' => hf p hp ((hull p).1 hp')

private theorem image_h (f : Point ≃ₗ[ℝ] Point) (P : Finset Point) :
    h (P.image f) = h P := by
  classical
  unfold h
  congr 1
  ext n
  change (n = 0 ∨ _) ↔ n = 0 ∨ _
  constructor
  · rintro (rfl | ⟨S, hSP, hS, hn⟩)
    · exact Or.inl rfl
    · let T := S.image f.symm
      have ht : T.image f = S := by
        simp [T, Finset.image_image, Function.comp_def]
      have hTP : T ⊆ P := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (hSP hq)
        simpa using hr
      apply Or.inr
      refine ⟨T, hTP, (image_convexPosition_iff f T).1 (by simpa only [ht] using hS), ?_⟩
      rw [← hn, ← ht, Finset.card_image_of_injective T f.injective]
  · rintro (rfl | ⟨S, hSP, hS, hn⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨S.image f, Finset.image_subset_image hSP,
        (image_convexPosition_iff f S).2 hS,
        (Finset.card_image_of_injective S f.injective).trans hn⟩

/-- Cardinality, general position, and the maximum size of a convex subset are
all preserved when a shear makes the horizontal coordinates distinct. -/
theorem distinctAbscissae_reduction {P : Finset Point} (hP : GeneralPosition P) :
    ∃ Q : Finset Point, GeneralPosition Q ∧ DistinctAbscissae Q ∧
      Q.card = P.card ∧ h Q = h P := by
  classical
  let bad : Finset ℝ := (P ×ˢ P).image fun pq => (pq.2.1 - pq.1.1) / (pq.1.2 - pq.2.2)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let f := shear t
  refine ⟨P.image f, ?_, ?_, Finset.card_image_of_injective P f.injective, image_h f P⟩
  · intro a ha b hb c hc hab hac hbc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hc
    exact fun hzero => hP p hp q hq r hr
      (fun h => hab (congrArg f h)) (fun h => hac (congrArg f h))
      (fun h => hbc (congrArg f h)) ((shear_orientation t p q r).symm.trans hzero)
  · intro a ha b hb heq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    change p.1 + t * p.2 = q.1 + t * q.2 at heq
    by_cases hs : p.2 = q.2
    · have hx : p.1 = q.1 := by rw [hs] at heq; linarith
      exact congrArg f (Prod.ext hx hs)
    · exact False.elim <| ht <| Finset.mem_image.mpr
        ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩,
          (div_eq_iff (sub_ne_zero.mpr hs)).2 (by linarith)⟩

end ESVerify
