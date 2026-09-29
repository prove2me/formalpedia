-- Prove2me | solution 1 for HermitianBianchi.det_gramMatrix
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:15:48.448604+00:00
-- url     : https://prove2.me/submissions/f70aadd1-482e-4843-816a-3dee504e36ce

-- Sol generated from Applications/Algebra/HermitianBianchiDiscriminant.lean
import Mathlib
import Definitions.Def_Applications_Algebra_HermitianBianchiDiscriminant
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Discriminant of the Hermitian Bianchi lattice `S_K = Herm₂(O_K)`

Let `d < 0` be squarefree, `K = ℚ(√d)`, and `O_K = ℤ[ω]` with
`ω = √d` if `d ≢ 1 [ZMOD 4]` and `ω = (1 + √d)/2` if `d ≡ 1 [ZMOD 4]`.

The rank-four lattice `S_K = Herm₂(O_K)` of Hermitian `2 × 2` matrices
`A = !![a, b; conj b, c]` (with `a, c ∈ ℤ`, `b ∈ O_K`) carries the quadratic
form `q(A) = 2 · det A`.  Writing `b = x + y·ω` in the basis given by the two
diagonal Hermitian matrix units together with the off-diagonal generators `1`
and `ω`, the lattice is coordinatised by `(a, c, x, y) ∈ ℤ⁴` and

  `q(a, c, x, y) = 2ac - 2 N(x + y ω) = 2ac - 2x² - 2T·xy - 2M·y²`,

where `T = Tr(ω) = ω + conj ω` and `M = N(ω) = ω · conj ω`.

This file builds the integral symmetric bilinear form `bil` whose diagonal is
`q` (its polarisation), assembles the Gram matrix in the four basis vectors,
and proves that its determinant equals the *fundamental discriminant*
`D_K = d` if `d ≡ 1 [ZMOD 4]` and `D_K = 4d` otherwise.

The Gram determinant turns out to equal `T² - 4M`, a purely algebraic identity;
the number-theoretic content is the evaluation `T² - 4M = D_K` for the two
shapes of `ω`.

## Main results
* `HermitianBianchi.bil_polar` : `bil` is the polarisation of `q`.
* `HermitianBianchi.qform_eq_two_hermDet` : `q = 2 · det` of the Hermitian matrix.
* `HermitianBianchi.det_gramMatrix` : `det (Gram T M) = T² - 4M`.
* `HermitianBianchi.discriminant_S_K` : the conjecture, in the form
  `det (Gram(S_K)) = D_K`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): det Gram(S_K) equals the fundamental discriminant D_K.
Experiment (Experimenter): coordinatise S_K by (a,c,x,y); the polar bilinear
  form gives a block-diagonal Gram matrix — a hyperbolic block !![0,1;1,0] for
  the diagonal units and a binary block !![-2,-T;-T,-2M] for the off-diagonal
  norm form.  Its determinant is (-1)·(4M - T²) = T² - 4M.
Analysis (Analyst): T² - 4M is exactly the discriminant of the minimal
  polynomial of ω, hence equals D_K (1 - (1-d) = d in the `d ≡ 1` case,
  0 - 4(-d) = 4d otherwise).  The hypothesis SURVIVED, and the proof reveals the
  identity is algebraic in (T, M); the negativity/squarefreeness of d are only
  needed to interpret T² - 4M as the field discriminant.
Critique (Critic): the determinant is genuinely symbolic in T, M (not a finite
  `decide`); the `d ≡ 1` branch needs the exact division (1-d)/4, handled by an
  integrality side-goal via `omega`.  No vacuous hypotheses: the equality is a
  nontrivial polynomial identity verified by `ring` after a block expansion.
Synthesis (PI): exported as `det_gramMatrix` (algebraic core) and
  `discriminant_S_K` (number-field statement).
-/

open Matrix

open HermitianBianchi









/-- Explicit shape of the Gram matrix: a hyperbolic block on the diagonal units
and the binary norm form `!![-2,-T;-T,-2M]` on the off-diagonal generators. -/
lemma gramMatrix_eq (T M : ℤ) :
    gramMatrix T M = !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, -2, -T; 0, 0, -T, -2 * M] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramMatrix, bil, Pi.single, Function.update]









open HermitianBianchi in
theorem solution(T M : ℤ) : (gramMatrix T M).det = T ^ 2 - 4 * M := by
  rw [gramMatrix_eq,
    show (!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, -2, -T; 0, 0, -T, -2 * M] :
          Matrix (Fin 4) (Fin 4) ℤ)
        = ((Matrix.fromBlocks (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) 0 0
            (!![-2, -T; -T, -2 * M])).reindex finSumFinEquiv finSumFinEquiv) from by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.reindex_apply, Matrix.submatrix_apply, Fin.addCases,
              finSumFinEquiv, Matrix.fromBlocks]]
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  ring
