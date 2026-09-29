-- Prove2me | Definitions.Def_Bridges_old_FunctionalCalculus
-- name    : Bridges_old_FunctionalCalculus
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:45.674145+00:00
-- url     : https://prove2.me/theorems/693a043c-862b-4b3e-a80b-92157f8a44ba
-- title:
--   Aether Catalog definitions — Bridges_old_FunctionalCalculus
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.old.FunctionalCalculus`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/old/FunctionalCalculus.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-! # Functional Calculus and Spectral Mapping for Hermitian Matrices

This file defines the continuous functional calculus for Hermitian matrices via
diagonalization and proves the spectral mapping theorem.

## Main results

* `continuousFunctionalCalculus` — Apply any function `f : ℝ → ℂ` to a Hermitian matrix
  via `U * diagonal(f ∘ eigenvalues) * U^*`.
* `polynomial_spectral_mapping` — The spectrum of `p(A)` is `p` applied to the spectrum of `A`,
  for polynomial `p` and any matrix `A`.
* `cfc_eigenvalues` — The eigenvalues of `f(A)` are `f` applied to eigenvalues of `A`.
* `isHermitian_of_real_cfc` — If `f` maps reals to reals, then `f(A)` is Hermitian.

## Tags

functional calculus, spectral mapping, polynomial, Hermitian matrix
-/

open Matrix Finset Complex Polynomial

noncomputable section

namespace SpectralTheory

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## Continuous Functional Calculus via Diagonalization -/

/-- Apply a function `f : ℝ → ℂ` to a Hermitian matrix via diagonalization:
`f(A) = U * diagonal(f ∘ eigenvalues) * U^*`. -/
def continuousFunctionalCalculus
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => f (hA.eigenvalues i)) *
    star (hA.eigenvectorUnitary : Matrix n n ℂ)

/-
The CFC of a Hermitian matrix applied to the identity function recovers the original matrix.
-/

/-
The CFC of a constant function is a scalar matrix.
-/

/-
The CFC is multiplicative: `f(A) * g(A) = (f * g)(A)`.
-/

/-
The CFC is additive: `f(A) + g(A) = (f + g)(A)`.
-/

/-
If `f` maps reals to reals, then `f(A)` is Hermitian.
-/

/-! ## Spectral Mapping -/

/-
The spectrum of `p(A)` equals `p` applied to the spectrum of `A`,
for any polynomial `p` and matrix `A` over an algebraically closed field.
-/

/-
The spectrum of a Hermitian matrix is real: it equals the range of the eigenvalue function
under `ofReal`.
-/

end SpectralTheory


