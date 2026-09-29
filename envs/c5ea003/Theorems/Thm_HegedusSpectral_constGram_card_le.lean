-- Prove2me | Theorems.Thm_HegedusSpectral_constGram_card_le
-- name    : HegedusSpectral.constGram_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:58:46.978286+00:00
-- url     : https://prove2.me/theorems/a86222e6-6343-40c8-a00e-56c16ed06497
-- title:
--   Hegedűs spectral bound for constant-pattern families.
-- statement:
--   **Hegedűs spectral bound for constant-pattern families.**  If a family of `m`
--   vectors in `ℝ^n` has constant self inner product `k` and constant pairwise inner
--   product `λ` with `0 ≤ λ < k`, then `m ≤ n`.
--
--   The hypotheses force the Gram matrix into the constant pattern, whose eigenvalue
--   structure (positivity) is then exploited.
--
--   ```lean
--   theorem HegedusSpectral.constGram_card_le(v : Fin m → EuclideanSpace ℝ (Fin n)) (k lam : ℝ)
--       (hlam : 0 ≤ lam) (hkl : lam < k)
--       (hdiag : ∀ i, inner ℝ (v i) (v i) = k)
--       (hoff : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = lam) : m ≤ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SpectralBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SpectralBound.lean#L109

-- Thm stub generated from Novelty/SpectralBound.lean
import Mathlib
import Definitions.Def_Novelty_SpectralBound
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hegedűs-type spectral bounds for combinatorial families

This file develops the *linear-algebra (spectral) bound* underlying Hegedűs'
eigenvalue condition: a finite family of vectors whose **Gram matrix** satisfies a
positivity (eigenvalue) constraint must be small — its cardinality is bounded by
the ambient dimension.

The engine is the equivalence between

* positive-definiteness of the Gram matrix `Matrix.gram ℝ v` (equivalently: all
  Gram eigenvalues are strictly positive), and
* linear independence of the family `v`,

which, combined with the rank bound `LinearIndependent.fintype_card_le_finrank`,
yields the size bound `m ≤ n`.

We then isolate the **constant-pattern** Gram matrix `(k - λ)·I + λ·J` and show it
is positive definite whenever `0 ≤ λ < k`, by splitting it as a positive-definite
multiple of the identity plus a positive-semidefinite multiple of the all-ones
matrix.  This is the algebraic core of the Fisher / Frankl–Wilson type bounds
proved in `EquiangularFisher.lean`.

## Menu-balance declaration

This cycle's target is a **cross-domain bridge**: it connects
*Combinatorics* (extremal families of sets, cf. the catalog file
`Novelty/CrossIntersectingProductBound.lean`) with
*Linear Algebra / Spectral theory* (Gram matrices, positive definiteness, and
eigenvalues from Mathlib's `Matrix.PosDef` API).
-/

open Matrix

open HegedusSpectral

variable {n m : ℕ}



/-! ## The general spectral bound -/



/-! ## The constant-pattern Gram matrix -/

theorem HegedusSpectral.constGram_card_le(v : Fin m → EuclideanSpace ℝ (Fin n)) (k lam : ℝ)
    (hlam : 0 ≤ lam) (hkl : lam < k)
    (hdiag : ∀ i, inner ℝ (v i) (v i) = k)
    (hoff : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = lam) : m ≤ n := by sorry
