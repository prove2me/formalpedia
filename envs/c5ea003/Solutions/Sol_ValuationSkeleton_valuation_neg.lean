-- Prove2me | solution 1 for ValuationSkeleton.valuation_neg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:52:16.955521+00:00
-- url     : https://prove2.me/submissions/6296d228-133d-40bb-962f-c33f69eea5d9

-- Sol generated from Bridges/ValuationSkeletonDuality/Core.lean
import Mathlib
import Definitions.Def_Bridges_ValuationSkeletonDuality_Core

/-!
# Valuation-Skeleton Margin Duality for p-adic Rational Networks — Core

This file establishes a valuation-theoretic margin theory for arithmetic rational
networks over non-Archimedean fields, connecting Berkovich-style skeleton decompositions
to certified ML robustness, tropical piecewise-linearization, and post-quantum
complexity proxies.

## Mathematical Domains Bridged
1. **Non-Archimedean Analytic Geometry** ↔ **Certified ML Robustness**
2. **Tropical Geometry** ↔ **Arithmetic Operadic Networks**
3. **Berkovich Skeleta** ↔ **Post-Quantum / Lattice Complexity**

Bridge: connects non-Archimedean analytic geometry to certified robustness in ML,
tropical piecewise-linearization to arithmetic operadic networks, and Berkovich
skeleta to post_quantum_security / lattice-style complexity proxies.
-/

open Finset Function Classical

noncomputable section

attribute [local instance] Classical.propDecidable

open ValuationSkeleton

/-! ## §1. Extended Valuation Codomain and HasIntValuation Typeclass -/



variable {K : Type*} [Field K] [HasIntValuation K]
variable {α : Type*}

/-! ## §2. Primitive Valuation Lemmas -/



/-
Valuation of negation equals valuation.
    Bridge: connects additive symmetry to tropical geometry invariance.
-/

/-
The valuation of a nonzero element is finite.
    Bridge: connects field non-degeneracy to tropical finiteness.
-/

/-
Inversion negates valuation away from zero.
    Bridge: connects field inversion to tropical negation.
-/

/-
Strict dominance: if v(x) < v(y), then v(x+y) = v(x).
    Bridge: connects strict ultrametric inequality to tropical monomial selection.
-/

/-! ## §3. Threshold Margin and Label Definitions -/





/-! ## §4. Skeleton Cell and Finite Cover Structures -/








/-! ## §5. Rational Gate Syntax -/


open RationalGate











/-! ## §6. Counting and Complexity Theorems -/




/-! ## §7. Chart Evaluation Cost Model -/




/-! ## §8. Refinement and Entropy -/




/-! ## §9. Valuation Lipschitz and Robustness -/





/-! ## §10. Gate Complexity Bound -/



/-
Gate complexity ≤ 2^(gateCount).
    Bridge: connects circuit depth to skeleton complexity.
-/



/-! ## §11. Tropical Margin Profile -/




/-! ## §12. High-Margin Label Constancy -/



/-! ## §13. Reparametrization and Symmetry -/







/-! ## §14. Robustness from Margin -/


/-! ## §15. Total Evaluation Cost -/


/-! ## §16. Quantified Existence Theorems -/


/-! ## §17. Addition and Multiplication Margin -/



/-! ## §18. Constant Gate Margin -/


/-! ## §19. Tropicalized Margin Is Min-Plus Affine -/


/-! ## §20. Security Proxy Monotonicity -/


/-! ## §21. Label Change Cells Finite -/


/-! ## §22. Affine Constancy on Cells -/


/-! ## §23. Depth-Zero Gates Have Trivial Complexity -/



/-! ## §24. HighMarginRegion Monotonicity -/


/-! ## §25. Pole-Free Composition -/



/-! ## §26. Valuation Label Constancy -/


/-! ## §27. CellConst Implies No Mixed Labels -/



open ValuationSkeleton in
theorem solution(x : K) :
    HasIntValuation.v (-x) = HasIntValuation.v x := by
  obtain ⟨ v, hv ⟩ := ‹HasIntValuation K›;
  rename_i h₁ h₂ h₃ h₄;
  have := h₁.map_mul ( -1 ) ( -1 ) ; simp_all +decide;
  have := h₃ ( -x ) ( -1 ) ; simp_all +decide;
  cases h : h₁.v ( -1 ) <;> simp_all +decide [ add_comm ];
  · cases h₁;
    rename_i h₁ h₂ h₃ h₄;
    cases this.symm.trans h₂;
  · have := h₁.map_one; simp_all +decide [ WithTop.some_eq_coe ] ;
    norm_cast at * ; simp_all +decide [ ← two_mul ];
    have := h₁.map_mul ( -x ) ( -1 ) ; simp_all +decide [ add_comm ] ;
