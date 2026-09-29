-- Prove2me | Definitions.Def_Bridges_TropicalRadonDuality
-- name    : Bridges_TropicalRadonDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:48.313641+00:00
-- url     : https://prove2.me/theorems/11854c0d-654e-4116-93c4-df5ab85fb0c2
-- title:
--   Aether Catalog definitions — Bridges_TropicalRadonDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalRadonDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalRadonDuality.lean by skeleton subtraction
import Mathlib
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

/-- The tropical Radon transform (sup-plus convention).
    Maps a function `f : X → ℤ` to its tropical inner products with each `h`. -/
def tropicalRadon (H : Finset (X → ℤ)) (f : X → ℤ) : (X → ℤ) → ℤ :=
  fun h => Finset.sup' Finset.univ Finset.univ_nonempty (fun x => f x + h x)

/-- The tropical adjoint/reconstruction operator (inf-minus convention).
    Maps measurement data `F` back to a function on `X`. -/
def tropicalAdjoint (H : Finset (X → ℤ)) (hH : H.Nonempty) (F : (X → ℤ) → ℤ) : X → ℤ :=
  fun x => Finset.inf' H hH (fun h => F h - h x)

/-- A function is in **tropical normal form** if it equals its own
    reconstruction from its Radon data. -/
def IsTropicalNormalForm (H : Finset (X → ℤ)) (hH : H.Nonempty) (f : X → ℤ) : Prop :=
  tropicalAdjoint H hH (tropicalRadon H f) = f

/-- `F` is **tropical support data** if Radon ∘ Adjoint reproduces it on H. -/
def IsTropicalSupportData (H : Finset (X → ℤ)) (hH : H.Nonempty) (F : (X → ℤ) → ℤ) : Prop :=
  ∀ h ∈ H, tropicalRadon H (tropicalAdjoint H hH F) h = F h

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


/-! ## Theorem D: Certified Reconstruction -/



/-! ## Theorem C: Minimal Separating Subfamily -/


/-
The Radon transform determines normal-form functions: any B ⊆ H that is nonempty
    makes the Radon transform injective on B-normal-form functions.
-/

/-
There exists an inclusion-minimal nonempty subfamily B ⊆ H such that every element
    of H can be dropped from B while preserving the normal-form injectivity property,
    but B itself cannot be further reduced. Concretely, B is the result of greedily
    removing redundant directions.
-/

end


