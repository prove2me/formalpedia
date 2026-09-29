-- Prove2me | Theorems.Thm_mem_range_tropicalRadon_iff_supportData
-- name    : mem_range_tropicalRadon_iff_supportData
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:34:29.649972+00:00
-- url     : https://prove2.me/theorems/0e30ae62-4407-4f2d-a468-b7e7fc8fea32
-- title:
--   Mem range tropicalRadon iff supportData
-- statement:
--   Formal statement of `mem_range_tropicalRadon_iff_supportData` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem mem_range_tropicalRadon_iff_supportData(H : Finset (X → ℤ)) (hH : H.Nonempty)
--       (F : (X → ℤ) → ℤ) :
--       (∃ f, IsTropicalNormalForm H hH f ∧ ∀ h ∈ H, tropicalRadon H f h = F h) ↔
--       IsTropicalSupportData H hH F := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalRadonDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalRadonDuality.lean#L171

-- Thm stub generated from Bridges/TropicalRadonDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalRadonDuality
/-
# Tropical Radon Transform Duality via Idempotent Semimodules

This module formalizes a finite theory of **tropical Radon transforms** and proves
a suite of duality, reconstruction, and minimality theorems that together create
a new bridge between tropical/idempotent algebra and integral geometry.

## Cross-Domain Connections

This work simultaneously touches:
- **Integral geometry**: tropical analogue of Radon/support transforms.
- **Convex geometry**: support-function duality for tropical convex bodies.
- **Order theory**: Galois connections and residuation.
- **Inverse problems**: certified reconstruction from partial observations.
- **Optimization**: semiring version of Fenchel duality.
- **Information theory**: minimal sufficient measurement families.

## Main Results

- `tropicalRadon_adjoint_gc`: The tropical Radon transform and its adjoint
  reconstruction operator form a Galois connection (residuated pair).
- `tropicalRadon_mono`, `tropicalAdjoint_mono`: Both operators are monotone.
- `tropicalAdjoint_tropicalRadon_ge`: f ≤ Adjoint(Radon(f)), the "convexification".
- `tropicalRadon_tropicalAdjoint_le`: Radon(Adjoint(F)) ≤ F on H.
- `tropicalRadon_adjoint_tropicalRadon`: Radon ∘ Adjoint ∘ Radon = Radon on H.
- `tropicalAdjoint_tropicalRadon_tropicalAdjoint`: Adjoint ∘ Radon ∘ Adjoint = Adjoint.
- `tropicalRadon_injective_on_normalForm`: Injectivity on the normal-form class.
- `tropicalRadon_reconstruct_normalForm`: Certified reconstruction for normal forms.
- `mem_range_tropicalRadon_iff_supportData`: Exact image characterization.
- `exists_minimal_separating_subfamily`: Existence of a minimal determining family.

## Convention

We use the **sup-plus** convention throughout:
  Radon_H(f)(h) = sup_{x ∈ X} (f(x) + h(x))

This is the tropical analogue of the Legendre–Fenchel transform, and we prove
duality with the **inf-minus** adjoint:
  Adjoint_H(F)(x) = inf_{h ∈ H} (F(h) - h(x))
-/


noncomputable section

open Finset Function

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-! ## Core Definitions -/





/-! ## The Galois Connection (Theorem B core)

The tropical Radon transform and its adjoint form a Galois connection:
  (∀ h ∈ H, Radon(f)(h) ≤ F(h)) ↔ (∀ x, f(x) ≤ Adjoint(F)(x))

This is the finite idempotent analogue of Legendre–Fenchel duality.
-/


/-! ## Monotonicity -/



/-! ## Closure Properties -/

/-
f ≤ Adjoint(Radon(f)): the closure is always above the original.
-/

/-
Radon(Adjoint(F))(h) ≤ F(h) for h ∈ H.
-/

/-
Radon ∘ Adjoint ∘ Radon = Radon on H.
-/

/-
Adjoint ∘ Radon ∘ Adjoint = Adjoint.
-/

/-! ## Theorem A: Injectivity on Normal Forms -/


/-! ## Theorem B: Image Characterization -/

theorem mem_range_tropicalRadon_iff_supportData(H : Finset (X → ℤ)) (hH : H.Nonempty)
    (F : (X → ℤ) → ℤ) :
    (∃ f, IsTropicalNormalForm H hH f ∧ ∀ h ∈ H, tropicalRadon H f h = F h) ↔
    IsTropicalSupportData H hH F := by sorry
