import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false

namespace ESVerify

variable {α : Type*}

/-- The split of a longest chain into a prefix and suffix, with bounds on their
lengths from the joining rank and from their prescribed endpoints. -/
def SectionFourSplit (G : Finset α) (len : Finset α → ℕ) (M r : ℕ)
    (prefixAt suffixAt : α → ℕ) : Prop :=
  ∀ ⦃H : Finset α⦄, H.Nonempty → H ⊆ G →
    ∃ p ∈ H, ∃ q ∈ H, ∃ a b : ℕ,
      len H = a + b ∧ a ≤ r ∧ b + r ≤ M ∧ a ≤ prefixAt p ∧ b ≤ suffixAt q

private theorem half_fail_or_both (G : Finset α) (hne : G.Nonempty)
    (P Q : α → Prop) :
    (∃ p ∈ G, P p ∧ Q p) ∨
      ∃ H ⊆ G, H.Nonempty ∧ G.card ≤ 2 * H.card ∧
        ((∀ p ∈ H, ¬ P p) ∨ ∀ p ∈ H, ¬ Q p) := by
  classical
  by_cases h : ∃ p ∈ G, P p ∧ Q p
  · exact Or.inl h
  right
  let F := G.filter (fun p => ¬ P p)
  let K := G.filter (fun p => ¬ Q p)
  have hcover : F ∪ K = G := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
    · intro hp
      by_cases hp' : P p
      · exact Finset.mem_union_right F (Finset.mem_filter.mpr ⟨hp, fun hq => h ⟨p, hp, hp', hq⟩⟩)
      · exact Finset.mem_union_left K (Finset.mem_filter.mpr ⟨hp, hp'⟩)
  have hsum : G.card ≤ F.card + K.card := by
    rw [← hcover]
    exact Finset.card_union_le (s := F) (t := K)
  have hg := Finset.card_pos.mpr hne
  by_cases hf : G.card ≤ 2 * F.card
  · exact ⟨F, Finset.filter_subset _ _, Finset.card_pos.mp (by omega), hf,
      Or.inl (fun _ hp => (Finset.mem_filter.mp hp).2)⟩
  · exact ⟨K, Finset.filter_subset _ _, Finset.card_pos.mp (by omega), by omega,
      Or.inr (fun _ hp => (Finset.mem_filter.mp hp).2)⟩

private theorem split_prefix_failure {G H : Finset α} {len : Finset α → ℕ}
    {M r : ℕ} {prefixAt suffixAt : α → ℕ} {η : ℝ}
    (hsplit : SectionFourSplit G len M r prefixAt suffixAt) (hne : H.Nonempty) (hHG : H ⊆ G)
    (hfail : ∀ p ∈ H, ¬ (r : ℝ) - η ≤ prefixAt p) : (len H : ℝ) < (M : ℝ) - η := by
  obtain ⟨p, hp, q, _, a, b, hlen, _, hb, ha', _⟩ := hsplit hne hHG
  have hbad := lt_of_not_ge (hfail p hp)
  have hbr : (b : ℝ) + r ≤ M := by exact_mod_cast hb
  have har : (a : ℝ) ≤ prefixAt p := by exact_mod_cast ha'
  rw [hlen, Nat.cast_add]
  linarith

private theorem split_suffix_failure {G H : Finset α} {len : Finset α → ℕ}
    {M r : ℕ} {prefixAt suffixAt : α → ℕ} {η : ℝ}
    (hsplit : SectionFourSplit G len M r prefixAt suffixAt) (hne : H.Nonempty) (hHG : H ⊆ G)
    (hfail : ∀ p ∈ H, ¬ (M : ℝ) - r - η ≤ suffixAt p) : (len H : ℝ) < (M : ℝ) - η := by
  obtain ⟨p, _, q, hq, a, b, hlen, ha, _, _, hb'⟩ := hsplit hne hHG
  have hbad := lt_of_not_ge (hfail q hq)
  have har : (a : ℝ) ≤ r := by exact_mod_cast ha
  have hbr : (b : ℝ) ≤ suffixAt q := by exact_mod_cast hb'
  rw [hlen, Nat.cast_add]
  linarith

/-- Proposition 4.2, from the four chain splits and the cap/cup concatenation bound. -/
theorem sectionFourAlternative {X G₁ G₂ : Finset α} {cap cup height : Finset α → ℕ}
    {x₁ y₁ x₂ y₂ : ℕ} {capStart₁ capEnd₁ cupStart₁ cupEnd₁ : α → ℕ}
    {capStart₂ capEnd₂ cupStart₂ cupEnd₂ : α → ℕ}
    (hsub₁ : G₁ ⊆ X) (hsub₂ : G₂ ⊆ X) (hne₁ : G₁.Nonempty) (hne₂ : G₂.Nonempty)
    (hcap : Monotone cap) (hcup : Monotone cup)
    (hcap₁ : SectionFourSplit G₁ cap (cap X) x₁ capStart₁ capEnd₁)
    (hcup₁ : SectionFourSplit G₁ cup (cup X) y₁ cupStart₁ cupEnd₁)
    (hcap₂ : SectionFourSplit G₂ cap (cap X) x₂ capStart₂ capEnd₂)
    (hcup₂ : SectionFourSplit G₂ cup (cup X) y₂ cupStart₂ cupEnd₂)
    (hjoin : ∀ p ∈ G₁, ∀ q ∈ G₂,
      capStart₁ p + capEnd₂ q + cupStart₁ p + cupEnd₂ q + 2 ≤ height X)
    (η : ℝ) :
    (cap X : ℝ) + cup X - ((x₂ : ℝ) + y₂ - ((x₁ : ℝ) + y₁)) - 4 * η + 2 ≤ height X ∨
    ∃ G ∈ ({G₁, G₂} : Set (Finset α)), ∃ H ⊆ G,
      H.Nonempty ∧ G.card ≤ 2 * H.card ∧
      (cap H : ℝ) + cup H < (cap X : ℝ) + cup X - η := by
  classical
  rcases half_fail_or_both G₁ hne₁ (fun p => (x₁ : ℝ) - η ≤ capStart₁ p)
      (fun p => (y₁ : ℝ) - η ≤ cupStart₁ p) with ⟨p, hp, hpc, hpu⟩ | h₁
  · rcases half_fail_or_both G₂ hne₂ (fun q => (cap X : ℝ) - x₂ - η ≤ capEnd₂ q)
        (fun q => (cup X : ℝ) - y₂ - η ≤ cupEnd₂ q) with ⟨q, hq, hqc, hqu⟩ | h₂
    · left
      have hj : (capStart₁ p : ℝ) + capEnd₂ q + cupStart₁ p + cupEnd₂ q + 2 ≤ height X := by
        exact_mod_cast hjoin p hp q hq
      linarith
    · right
      obtain ⟨H, hHG, hne, hhalf, hfail | hfail⟩ := h₂
      · refine ⟨G₂, by simp, H, hHG, hne, hhalf, ?_⟩
        have hlen := split_suffix_failure hcap₂ hne hHG hfail
        have hother : (cup H : ℝ) ≤ cup X := by exact_mod_cast hcup (hHG.trans hsub₂)
        linarith
      · refine ⟨G₂, by simp, H, hHG, hne, hhalf, ?_⟩
        have hlen := split_suffix_failure hcup₂ hne hHG hfail
        have hother : (cap H : ℝ) ≤ cap X := by exact_mod_cast hcap (hHG.trans hsub₂)
        linarith
  · right
    obtain ⟨H, hHG, hne, hhalf, hfail | hfail⟩ := h₁
    · refine ⟨G₁, by simp, H, hHG, hne, hhalf, ?_⟩
      have hlen := split_prefix_failure hcap₁ hne hHG hfail
      have hother : (cup H : ℝ) ≤ cup X := by exact_mod_cast hcup (hHG.trans hsub₁)
      linarith
    · refine ⟨G₁, by simp, H, hHG, hne, hhalf, ?_⟩
      have hlen := split_prefix_failure hcup₁ hne hHG hfail
      have hother : (cap H : ℝ) ≤ cap X := by exact_mod_cast hcap (hHG.trans hsub₁)
      linarith

/-- Corollary 4.3. Logarithmic losses are expressed as differences of base-two
logarithms of positive cardinalities. -/
theorem sectionFourShrink {X G₁ G₂ : Finset α} {v h : Finset α → ℝ} {W e gap : ℝ}
    (hsub₁ : G₁ ⊆ X) (hsub₂ : G₂ ⊆ X) (hne₁ : G₁.Nonempty) (hne₂ : G₂.Nonempty)
    (hW : 0 < W) (he : 0 ≤ e) (hdensity : Real.logb 2 X.card ≤ v X)
    (hgap : gap ≤ (W + v X - Real.logb 2 X.card) / 2)
    (hsize₁ : 1 + Real.logb 2 X.card - Real.logb 2 G₁.card ≤ e)
    (hsize₂ : 1 + Real.logb 2 X.card - Real.logb 2 G₂.card ≤ e)
    (halt : ∀ η > 0, v X - gap - 4 * η + 2 ≤ h X ∨
      ∃ G ∈ ({G₁, G₂} : Set (Finset α)), ∃ H ⊆ G,
        H.Nonempty ∧ G.card ≤ 2 * H.card ∧ v H < v X - η) :
    Real.logb 2 X.card ≤ h X + W + 4 * e ∨
    ∃ H ⊂ X, H.Nonempty ∧ Real.logb 2 X.card - Real.logb 2 H.card ≤ e ∧
      W + v H - Real.logb 2 H.card < (7 / 8 : ℝ) * (W + v X - Real.logb 2 X.card) := by
  let z := W + v X - Real.logb 2 X.card
  have hz : 0 < z := by dsimp [z]; linarith
  let η := z / 8 + e
  have hη : 0 < η := by dsimp [η]; linarith
  rcases halt η hη with hstop | ⟨G, hG, H, hHG, hH, hhalf, hdrop⟩
  · left
    dsimp [η, z] at hstop
    linarith
  · right
    have hGdata : G ⊆ X ∧ G.Nonempty ∧ 1 + Real.logb 2 X.card - Real.logb 2 G.card ≤ e := by
      rcases Set.mem_insert_iff.mp hG with rfl | hG'
      · exact ⟨hsub₁, hne₁, hsize₁⟩
      · have heq := Set.mem_singleton_iff.mp hG'
        subst G
        exact ⟨hsub₂, hne₂, hsize₂⟩
    obtain ⟨hGsub, hGne, hGsize⟩ := hGdata
    have hHpos : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hH
    have hGpos : (0 : ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hGne
    have hhalf' : (G.card : ℝ) ≤ (2 : ℝ) * H.card := by exact_mod_cast hhalf
    have hlog := Real.strictMonoOn_logb (show 1 < (2 : ℝ) by norm_num) |>.monotoneOn
      hGpos (by change 0 < (2 : ℝ) * H.card; positivity) hhalf'
    rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hHpos.ne', Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog
    have hloss : Real.logb 2 X.card - Real.logb 2 H.card ≤ e := by linarith
    refine ⟨H, Finset.ssubset_iff_subset_ne.mpr ⟨hHG.trans hGsub, ?_⟩, hH, hloss, ?_⟩
    · intro heq
      subst H
      linarith
    · dsimp [η, z] at hdrop
      linarith

end ESVerify
