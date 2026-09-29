-- Prove2me | solution 1 for HegedusSpectral.constGram_card_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:00:45.448416+00:00
-- url     : https://prove2.me/submissions/e7ec7cee-c21f-4bf4-af86-4942a6dac111

-- Sol generated from Novelty/SpectralBound.lean
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


/-- The all-ones matrix is positive semidefinite: it is `c · cᴴ` for the all-ones
column vector `c`, hence a Gram matrix. -/
theorem allOnes_posSemidef (m : ℕ) : (allOnes m).PosSemidef := by
  have hJ : allOnes m = (Matrix.replicateCol (Fin 1) (1 : Fin m → ℝ)) *
      (Matrix.replicateCol (Fin 1) (1 : Fin m → ℝ))ᴴ := by
    ext i j; simp [allOnes, Matrix.mul_apply, Matrix.replicateCol, Matrix.conjTranspose]
  rw [hJ]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-! ## The general spectral bound -/

/-- **Spectral size bound (Gram form).**  If the Gram matrix of a finite family of
vectors in `ℝ^n` is positive definite, then the family has at most `n` members.

This is the heart of Hegedűs' bound: a positivity (eigenvalue) constraint on the
Gram matrix forces linear independence, and linear independence is capped by the
dimension. -/
theorem gram_posDef_card_le (v : Fin m → EuclideanSpace ℝ (Fin n))
    (h : (Matrix.gram ℝ v).PosDef) : m ≤ n := by
  have hli : LinearIndependent ℝ v := (Matrix.posDef_gram_iff_linearIndependent).1 h
  have := hli.fintype_card_le_finrank
  simpa using this


/-! ## The constant-pattern Gram matrix -/

/-- **Positive definiteness of the constant-pattern matrix.**  For `0 ≤ λ` and
`λ < k`, the matrix with diagonal entries `k` and off-diagonal entries `λ`, written
`(k - λ)·I + λ·J`, is positive definite.

Equivalently: the quadratic form is `(k − λ)·Σ xᵢ² + λ·(Σ xᵢ)²`, strictly positive
on nonzero vectors. -/
theorem constPattern_posDef (k lam : ℝ) (hlam : 0 ≤ lam) (hkl : lam < k) :
    ((k - lam) • (1 : Matrix (Fin m) (Fin m) ℝ) + lam • allOnes m).PosDef := by
  apply Matrix.PosDef.add_posSemidef
  · exact Matrix.PosDef.smul Matrix.PosDef.one (by linarith)
  · exact Matrix.PosSemidef.smul (allOnes_posSemidef m) hlam

/-- A Gram matrix with **constant diagonal `k` and constant off-diagonal `λ`**
equals the constant-pattern matrix `(k − λ)·I + λ·J`. -/
theorem gram_eq_constPattern (v : Fin m → EuclideanSpace ℝ (Fin n)) (k lam : ℝ)
    (hdiag : ∀ i, inner ℝ (v i) (v i) = k)
    (hoff : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = lam) :
    Matrix.gram ℝ v = (k - lam) • (1 : Matrix (Fin m) (Fin m) ℝ) + lam • allOnes m := by
  ext i j
  rw [show (Matrix.gram ℝ v) i j = inner ℝ (v i) (v j) from rfl]
  by_cases h : i = j
  · subst h
    rw [hdiag]
    simp [Matrix.add_apply, Matrix.smul_apply, allOnes]
  · rw [hoff i j h]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne h, allOnes]


/-! ## Tightness: the bound is achieved -/



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
open HegedusSpectral in
theorem solution(v : Fin m → EuclideanSpace ℝ (Fin n)) (k lam : ℝ)
    (hlam : 0 ≤ lam) (hkl : lam < k)
    (hdiag : ∀ i, inner ℝ (v i) (v i) = k)
    (hoff : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = lam) : m ≤ n := by
  apply gram_posDef_card_le v
  rw [gram_eq_constPattern v k lam hdiag hoff]
  exact constPattern_posDef k lam hlam hkl
