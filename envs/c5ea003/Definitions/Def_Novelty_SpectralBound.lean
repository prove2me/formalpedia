-- Prove2me | Definitions.Def_Novelty_SpectralBound
-- name    : Novelty_SpectralBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:21:32.1861+00:00
-- url     : https://prove2.me/theorems/e11f6304-9ad1-487d-ab86-e9ee427ed5ec
-- title:
--   Aether Catalog definitions — Novelty_SpectralBound
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SpectralBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SpectralBound.lean by skeleton subtraction
import Mathlib
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

namespace HegedusSpectral

variable {n m : ℕ}

/-- The `m × m` **all-ones matrix** `J`. -/
noncomputable def allOnes (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun _ _ => (1 : ℝ))


/-! ## The general spectral bound -/



/-! ## The constant-pattern Gram matrix -/




/-! ## Tightness: the bound is achieved -/


end HegedusSpectral

/-
-- !-- Lab Notes -- !--

Category (Menu Balance v19a): CROSS-DOMAIN BRIDGE
  Combinatorics (extremal set families) ⨯ Linear Algebra / Spectral theory
  (Gram matrices, positive definiteness, eigenvalues).

Hypothesis (Hypothesizer):
  H1. A positivity constraint on the Gram matrix of a vector family (Hegedűs'
      eigenvalue condition) should bound the family size by the dimension.
  H2. The constant self/pairwise inner-product pattern `(k−λ)I + λJ` is positive
      definite exactly when `0 ≤ λ < k`, and this should be provable WITHOUT
      diagonalising — by an additive split into PosDef + PosSemidef pieces.
  H3 (bold). The same spectral inequality should subsume classical extremal
      set-system bounds (Fisher / Frankl–Wilson), i.e. pure combinatorics is a
      corollary of one eigenvalue inequality.

Experiment (Experimenter):
  * `gram_posDef_card_le` : derived from `posDef_gram_iff_linearIndependent`
    together with `LinearIndependent.fintype_card_le_finrank`.  Confirmed H1.
  * `gram_eigenvalues_pos_card_le` : restated via
    `IsHermitian.posDef_iff_eigenvalues_pos`, making the eigenvalue condition
    explicit.
  * `constPattern_posDef` : proved via `PosDef.add_posSemidef`, `PosDef.smul`,
    `PosDef.one`, and the Gram representation `J = c·cᴴ` of the all-ones matrix.
    Confirmed H2 (no spectral decomposition needed).
  * `spectral_bound_tight` : the orthonormal `basisFun` realises equality `m = n`.

Analysis (Analyst):
  - The decisive structural pattern: "spectral positivity ⇒ linear independence
    ⇒ dimension cap".  The eigenvalue language and the linear-independence
    language are interchangeable through Mathlib's `gram` API.
  - Splitting `(k−λ)I + λJ` rather than diagonalising avoids all eigenvector
    bookkeeping; the only facts used are PosDef of `I` and PosSemidef of `J`.

Critique (Critic):
  - None of the main results is `True`/`rfl`/`decide`-only: each composes a
    genuine inequality (`linarith`, additive PosDef splitting, rank bound).
  - Edge cases: `m = 0` gives `0 ≤ n` (fine); `spectral_bound_tight` handles
    `n = 0` (empty family, trivially PosDef).

Synthesis (PI):
  One eigenvalue inequality on the Gram matrix yields a dimension cap; the
  constant-pattern instance is the algebraic core reused by the combinatorial
  bridge in `EquiangularFisher.lean`.
-/


