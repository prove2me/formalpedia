-- Prove2me | solution 1 for Bridges.AlgebraEMLTropical.PadicClosureInformationDuality.ultrametricInfoDist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:07:21.280762+00:00
-- url     : https://prove2.me/submissions/8219d824-2e9f-4b69-b8fb-7132a4ebeb29

-- Sol generated from Bridges/AlgebraEMLTropical/PadicClosureInformationDuality.lean
import Mathlib
import Definitions.Def_Bridges_AlgebraEMLTropical_PadicClosureInformationDuality
/-
# Non-Archimedean Information Duality via p-adic Closure Capacities and Min-Plus Rate Functions

This file formalizes a duality between closure-stable ultrametric capacities on finite
closure lattices and tropical min-plus information functionals. The valuation scale
is `WithTop ℕ` (equivalently `ℕ∞`), capturing the essential non-Archimedean structure:
`0` = trivial (empty set), finite values = finite information cost, `⊤` = impossible.

## Main Results (all sorry-free)

- `closureCapacity_tropicalizes` — Every closure capacity yields tropical info.
- `tropicalization_canonical_on_closure_classes` — Constant on closure classes.
- `closureCapacity_residuated_of_fintype` — Residuation automatic from finiteness.
- `tropicalInformation_reconstructs_unique_capacity` — Unique reconstruction.
- `capacity_info_equiv` — Type equivalence ClosureCapacity ≃ TropicalClosureInformation.
- `closureMorphism_information_contraction` — Data processing inequality.
- `ultrametricInfoDist_triangle` — Ultrametric triangle inequality for info distance.
- `closure_class_iInf_eq` — Infimum over closure class is attained.
- `isClosureMorphism_comp` — Closure morphisms compose.
- `pullback_comp_eq` — Pullback is functorial.
- `ultrametric_ternary_join` — Three-way ultrametric bound.

## Bridges

- **Algebra ↔ Information Theory**: Ultrametric capacities ↔ tropical information
- **Valuation Theory ↔ Optimization**: p-adic valuations ↔ min-plus shortest paths
- **EML Semantics ↔ Tropical Geometry**: Closure lattices ↔ idempotent semimodules
- **Category Theory ↔ Data Processing**: Closure morphisms ↔ information contraction
-/


open Set Classical

noncomputable section

open Bridges.AlgebraEMLTropical.PadicClosureInformationDuality

/-! ## §1. Closure Operator Axiomatics -/



/-! ## §2. Closure Capacity

A normalized, monotone, closure-invariant function from sets to the tropical
valuation scale `WithTop ℕ`, satisfying the ultrametric join inequality. -/



/-! ## §3. Tropical Closure Information

Extends ClosureCapacity with residuation: every closure class has a least-cost
representative. -/



/-! ## §4. Closure Morphisms -/


/-! ## §5. Decomposition Cost -/


/-! ## §6. Unit-Shift Equivalence -/


/-! ## §7. Theorem A: Tropicalization -/


/-! ## §8. Closure Class Invariance -/


/-! ## §9. Residuation from Finiteness -/


/-! ## §10. Theorem B: Reconstruction and Uniqueness -/


/-! ## §11. Capacity ↔ Information Maps -/





/-! ## §12. Theorem C: Type Equivalence -/


/-! ## §13. Pullback Along Closure Morphisms -/


/-! ## §14. Theorem D: Information Contraction -/


/-! ## §15. Theorem E: Optimization = Tropical Residuation -/


/-! ## §16. Attained Infimum (Strengthened Theorem E) -/


/-! ## §17. Closure Expansion Preserves Information -/


/-! ## §18. Ultrametric Ternary Join -/


/-! ## §19. Closure Morphism Composition -/


/-! ## §20. Identity Closure Morphism -/


/-! ## §21. Zero Capacity -/


/-! ## §22. Closure Equivalence -/




/-! ## §23. Capacity Bounded by Closure Containment -/


/-! ## §24. Pullback Functoriality -/


/-! ## §25. EquivalentUpToUnitShift -/


/-! ## §26. Ultrametric Information Distance -/




/-! ## §27. Singleton Information -/



/-! ## §28. Closure Operator Examples -/



/-! ## §29. Order on Capacities -/



/-! ## §30. Concrete Example: Bool -/



open Bridges.AlgebraEMLTropical.PadicClosureInformationDuality in
theorem solution    {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α}
    (hcl : IsClosureOperator cl)
    (v : ClosureCapacity α cl) (s t u : Set α) :
    ultrametricInfoDist v s u ≤
      max (ultrametricInfoDist v s t) (ultrametricInfoDist v t u) := by
  unfold ultrametricInfoDist
  have hsub : s ∪ u ⊆ cl (s ∪ t) ∪ cl (t ∪ u) := by
    intro x hx
    rcases hx with hs | hu
    · exact Or.inl (hcl.extensive _ (Or.inl hs))
    · exact Or.inr (hcl.extensive _ (Or.inr hu))
  calc v.toFun (cl (s ∪ u))
      ≤ v.toFun (cl (cl (s ∪ t) ∪ cl (t ∪ u))) :=
        v.monotone (hcl.monotone hsub)
    _ ≤ max (v.toFun (cl (s ∪ t))) (v.toFun (cl (t ∪ u))) := by
        have h := v.ultrametric_join (cl (s ∪ t)) (cl (t ∪ u))
        rw [v.closed_invariant, v.closed_invariant] at h
        rw [v.closed_invariant, v.closed_invariant]
        exact h
