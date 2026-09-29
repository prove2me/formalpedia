-- Prove2me | solution 1 for SheafProofStateDuality.exists_inclusion_minimal_nontrivial_support
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:42:19.876256+00:00
-- url     : https://prove2.me/submissions/38feff9e-d1da-42d3-be6d-ac6633a11d42

-- Sol generated from Bridges/SheafProofStateDuality.lean
import Mathlib
import Definitions.Def_Bridges_SheafProofStateDuality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Sheaf–Proof-State Duality via Finite Cohomological Obstruction Theory

A finite combinatorial theorem package: for proof-state dependency complexes,
failure of a globally coherent proof policy is *exactly* first cohomology,
and every nonzero obstruction yields an extractable minimal inconsistent cycle.

## Main Results

* `coboundary_is_cocycle` — every coboundary is a cocycle (δ² = 0)
* `global_section_iff_H1_trivial` — global extendability ↔ H¹ = 0
* `exists_inclusion_minimal_nontrivial_support` — minimal obstruction extraction
* `nontrivial_cocycle_lower_bounds_instability` — H¹ ≠ 0 ⟹ instability ≥ 1
* `finite_separation_holds` — finite separation for global sections
* `cohomological_vanishing_minimal_realization` — learnability/minimality duality
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

open SheafProofStateDuality

/-! ## §1. Proof Dependency Complex -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [DecidableEq M]

/-! ## §2. Cochains and Coboundary -/


/-! ## §3. Cocycles, Coboundaries, H¹ -/






/-! ## §4. Core Theorems -/

/-
**δ² = 0**: Every coboundary is a cocycle.
    Proof: `(f(j)-f(i)) + (f(k)-f(j)) = f(k)-f(i)`.
-/

/-
**Global extendability ↔ H¹ trivial** (definitional equivalence).
-/

/-
**H¹ nontrivial ↔ ¬ H¹ trivial.**
-/

/-! ## §5. Cohomology Classes -/


theorem sameCohomologyClass_refl (K : ProofDependencyComplex ι) (z : ι × ι → M) :
    SameCohomologyClass K z z := by
  exact ⟨ 0, by ext; simp +decide [ coboundary ] ⟩


/-! ## §6. Support and Minimal Obstruction Extraction -/



/-
**Certified Minimal Counterexample Reconstruction.**
    Any nontrivial cocycle has a cohomologous representative with
    inclusion-minimal nontrivial support. Follows by well-founded
    descent on the cardinality of support (finite).
-/

/-! ## §7. Instability Lower Bound -/



/-
**Nontrivial cocycle forces positive instability.**
    If `z` is not a coboundary, every predictor disagrees on ≥ 1 pair.
-/

/-
**H¹ nontrivial ⟹ positive instability bound.**
-/

/-! ## §8. Global Sections Subgroup -/



/-
Membership ↔ zero coboundary.
-/

/-
When `M` is finite, global sections form a finite set.
-/

/-! ## §9. Learnability / Minimality Duality -/



/-
Finite separation always holds for functions with decidable eq.
-/

/-
**Learnability/Minimality Duality.** The minimal architecture equals
    the global sections cardinality. Combined with H¹ = 0, this reduces
    proof-predictor realizability to a finite generation problem, which
    the catalog theorem `finite_separation_semimodule_realization_minimal`
    identifies with minimal generators.
-/

/-! ## §10. Obstruction Characterization -/

/-
Zero coboundary ↔ global section membership.
-/

/-
Extendability ↔ coboundary (definitional).
-/


open SheafProofStateDuality in
theorem solution    (K : ProofDependencyComplex ι) [∀ i j, Decidable (K.edge i j)]
    (z : ι × ι → M) (hz : ¬ IsCoboundary K z) :
    ∃ zmin : ι × ι → M,
      ¬ IsCoboundary K zmin ∧
      SameCohomologyClass K z zmin ∧
      cochainSupport K zmin ⊆ cochainSupport K z ∧
      InclusionMinimalNontrivialSupport K zmin := by
  -- By the well-foundedness of the natural numbers, there exists a minimal element in the set of supports of representatives of z.
  obtain ⟨zmin, hzmin⟩ : ∃ zmin : ι × ι → M, ¬ IsCoboundary K zmin ∧ SameCohomologyClass K z zmin ∧ cochainSupport K zmin ⊆ cochainSupport K z ∧ ∀ z' : ι × ι → M, ¬ IsCoboundary K z' → SameCohomologyClass K z z' → cochainSupport K z' ⊆ cochainSupport K z → (cochainSupport K zmin).card ≤ (cochainSupport K z').card := by
    have h_well_founded : ∃ s ∈ {s : Finset (ι × ι) | ∃ z' : ι × ι → M, ¬ IsCoboundary K z' ∧ SameCohomologyClass K z z' ∧ cochainSupport K z' = s ∧ s ⊆ cochainSupport K z}, ∀ t ∈ {s : Finset (ι × ι) | ∃ z' : ι × ι → M, ¬ IsCoboundary K z' ∧ SameCohomologyClass K z z' ∧ cochainSupport K z' = s ∧ s ⊆ cochainSupport K z}, s.card ≤ t.card := by
      apply_rules [ Set.exists_min_image ];
      · exact Set.toFinite _;
      · exact ⟨ _, ⟨ z, hz, sameCohomologyClass_refl K z, rfl, Finset.Subset.refl _ ⟩ ⟩;
    obtain ⟨ s, ⟨ z', hz', hz'', rfl, hs ⟩, hs' ⟩ := h_well_founded; exact ⟨ z', hz', hz'', hs, fun z'' hz'' hz''' hz'''' => hs' _ ⟨ z'', hz'', hz''', rfl, hz'''' ⟩ ⟩ ;
  refine' ⟨ zmin, hzmin.1, hzmin.2.1, hzmin.2.2.1, hzmin.1, _ ⟩;
  intro z' hz' hz'_same hz'_subset
  have h_card : (cochainSupport K zmin).card ≤ (cochainSupport K z').card := by
    apply hzmin.2.2.2 z' hz';
    · have h_trans : SameCohomologyClass K z zmin ∧ SameCohomologyClass K zmin z' → SameCohomologyClass K z z' := by
        rintro ⟨ h₁, h₂ ⟩;
        obtain ⟨ f, hf ⟩ := h₁
        obtain ⟨ g, hg ⟩ := h₂
        use f + g;
        unfold coboundary at *; simp_all +decide [ funext_iff ] ;
        grind;
      exact h_trans ⟨ hzmin.2.1, hz'_same ⟩;
    · exact Finset.Subset.trans hz'_subset hzmin.2.2.1;
  exact Finset.eq_of_subset_of_card_le hz'_subset h_card |> Eq.symm
