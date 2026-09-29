-- Prove2me | Definitions.Def_EML_ProductApproximation
-- name    : EML_ProductApproximation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:41.329575+00:00
-- url     : https://prove2.me/theorems/7ade926a-5b33-49ae-a155-7f84dbaf28dd
-- title:
--   Aether Catalog definitions — EML_ProductApproximation
-- statement:
--   Definition bundle for the Aether Catalog module `EML.ProductApproximation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/ProductApproximation.lean by skeleton subtraction
import Mathlib
/-
# Stone–Weierstrass for Compact Product Codomains via Factorwise Approximation

This file proves that if continuous maps into `Y` and into `Z` can each be uniformly
approximated from respective classes `AY` and `AZ`, then continuous maps into the
product `Y × Z` can be uniformly approximated by "paired" maps from `AY` and `AZ`.

The key insight is that Mathlib's product metric on `Y × Z` is the sup/max metric:
  `dist (a, b) (c, d) = max (dist a c) (dist b d)`
so coordinatewise `< ε` estimates immediately yield a product `< ε` estimate with
no need to split `ε/2`.

## Main results

- `dist_prod_mk_lt_of_lt`: coordinatewise `< ε` implies productwise `< ε`
- `ContinuousMap.prodMk_projFst_projSnd`: decomposition identity for maps into products
- `PairClass`: the set of paired maps from two approximation classes
- `pairClass_uniform_dense`: the main product approximation theorem
- `denseRange_pair_of_denseRange_fst_snd`: alternative formulation
- `eml_uniform_dense_prod`: specialization to any EML-like predicate
- `pairClass_uniform_dense_triple`: ternary product corollary

## References

The argument is the standard factorwise approximation + diagonal assembly strategy,
a routine consequence of the product (sup) metric structure.
-/


open scoped Topology
open ContinuousMap

noncomputable section

/-! ## §1. Product Metric Estimates -/



/-! ## §2. Coordinate Decomposition for Continuous Maps -/

/-- The projection of `f : C(X, Y × Z)` to the first coordinate. -/
def ContinuousMap.projFst {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y × Z)) : C(X, Y) :=
  ⟨fun x => (f x).1, continuous_fst.comp f.continuous⟩

/-- The projection of `f : C(X, Y × Z)` to the second coordinate. -/
def ContinuousMap.projSnd {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y × Z)) : C(X, Z) :=
  ⟨fun x => (f x).2, continuous_snd.comp f.continuous⟩


/-! ## §3. PairClass and the Main Approximation Theorem -/

/-- The class of continuous maps into `Y × Z` obtained by pairing a map from `AY`
with a map from `AZ`. -/
def PairClass
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (AY : Set (C(X, Y))) (AZ : Set (C(X, Z))) : Set (C(X, Y × Z)) :=
  {f | ∃ g ∈ AY, ∃ h ∈ AZ, f = ContinuousMap.prodMk g h}



/-! ## §4. Specialization to EML-like Predicates -/


/-! ## §5. Ternary Product Corollary -/


/-! ## §6. Closure Properties of PairClass -/




end


