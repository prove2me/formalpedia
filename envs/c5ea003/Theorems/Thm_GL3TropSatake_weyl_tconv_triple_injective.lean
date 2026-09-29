-- Prove2me | Theorems.Thm_GL3TropSatake_weyl_tconv_triple_injective
-- name    : GL3TropSatake.weyl_tconv_triple_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:35:39.162733+00:00
-- url     : https://prove2.me/theorems/ffc2c7c9-f02e-4b8b-9117-055b652ced26
-- title:
--   The Weyl triple (weylConv1, weylConv2, weylConv3) is injective.
-- statement:
--   The Weyl triple (weylConv1, weylConv2, weylConv3) is injective.
--   This follows because weylConv3 alone is injective (being a shift by the
--   central element (1,1,1), whose S₃-orbit is a singleton).
--
--   ```lean
--   theorem GL3TropSatake.weyl_tconv_triple_injective:
--       Function.Injective (fun f : TropFn => (weylConv1 f, weylConv2 f, weylConv3 f)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/NeuralCoding/GL3TropicalSatake.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/NeuralCoding/GL3TropicalSatake.lean#L323

-- Thm stub generated from Tropical/NeuralCoding/GL3TropicalSatake.lean
import Mathlib
import Definitions.Def_Tropical_NeuralCoding_GL3TropicalSatake
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# GL₃ Tropical Satake Uniqueness

## Main Results

We prove that a tropical function on the GL₃ dominant chamber is uniquely
determined by its tropical convolutions with rank-1 Levi test functions.

### Core Theorems

* `tconvDelta_injective` — Convolution with *any* dominant delta function is injective.
  This is the key algebraic fact: the dominant cone is closed under addition,
  so shifting by any dominant vector is a bijection on the dominant chamber.

* `gl3_tropical_satake_testFamily_injective` — The three-test-function operator
  `f ↦ (f ⊛ δ_{ω₁}, f ⊛ δ_{ω₂}, f ⊛ δ_{ω₃})` is injective, where ω₁, ω₂, ω₃
  are the fundamental coweights (1,0,0), (1,1,0), (1,1,1).

* `gl3_tropical_satake_testFamily_unique` — Extensional uniqueness: if two tropical
  functions agree on all three convolutions, they are equal.

* `weyl_tconv_triple_injective` — For the Weyl-symmetrized convolution (which takes
  max over S₃-orbits), the three fundamental coweight tests together still determine f.

### Mathematical Context

The tropical Satake correspondence identifies finitely-supported tropical functions on
dominant coweights with elements of the tropical spherical Hecke algebra. The injectivity
theorems here establish that the "evaluation at three generators" map is faithful — this
is the **operator separation principle** for the GL₃ tropical Hecke algebra.

The three test functions correspond to the three fundamental representations of GL₃:
- ω₁ = (1,0,0): the standard representation
- ω₂ = (1,1,0): the exterior square ∧²
- ω₃ = (1,1,1): the determinant representation
-/

open GL3TropSatake

/-! ## Section 1: Basic Types -/




/-! ## Section 2: Arithmetic on Integer Triples -/







/-! ## Section 3: Dominant Weight Arithmetic -/



/-! ## Section 4: Fundamental Coweights -/




/-! ## Section 5: Tropical Convolution with Delta Functions -/



/-! ## Section 6: Core Injectivity Theorem -/


/-! ## Section 7: Test Function Predicates -/

 -- positive second gap







/-! ## Section 8: Main Injectivity Theorems -/




/-! ## Section 9: Facet Valuations

We define the three facet valuation operators and prove they are determined
by the test function convolutions. -/








/-! ## Section 10: Weyl-Symmetrized Convolution

For the Weyl group W = S₃ of GL₃, the **Weyl-symmetrized** tropical convolution
is more natural from the representation-theoretic perspective. Here, δ_{ω₁}
contributes from all permutations of its weight, giving:

  (f ⊛_W δ_{ω₁})(wt) = max(f(sort(wt - e₁)), f(sort(wt - e₂)), f(sort(wt - e₃)))

where e₁, e₂, e₃ are the standard basis vectors and sort arranges components
in decreasing order. -/

theorem GL3TropSatake.weyl_tconv_triple_injective:
    Function.Injective (fun f : TropFn => (weylConv1 f, weylConv2 f, weylConv3 f)) := by sorry
