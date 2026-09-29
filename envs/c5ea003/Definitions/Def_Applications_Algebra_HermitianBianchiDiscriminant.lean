-- Prove2me | Definitions.Def_Applications_Algebra_HermitianBianchiDiscriminant
-- name    : Applications_Algebra_HermitianBianchiDiscriminant
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:41.968813+00:00
-- url     : https://prove2.me/theorems/f9384489-1203-4a94-a4e8-fab92706b98a
-- title:
--   Aether Catalog definitions — Applications_Algebra_HermitianBianchiDiscriminant
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Algebra.HermitianBianchiDiscriminant`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Algebra/HermitianBianchiDiscriminant.lean by skeleton subtraction
import Mathlib
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

namespace HermitianBianchi

/-- The quadratic form `q(a,c,x,y) = 2ac - 2x² - 2T·xy - 2M·y²` on `S_K`,
where `T = Tr ω`, `M = N ω`.  Equals `2 · det` of the Hermitian matrix. -/
def qform (T M : ℤ) (v : Fin 4 → ℤ) : ℤ :=
  2 * (v 0 * v 1) - 2 * (v 2) ^ 2 - 2 * T * (v 2 * v 3) - 2 * M * (v 3) ^ 2

/-- The integral symmetric bilinear form whose diagonal is `qform`. -/
def bil (T M : ℤ) (u v : Fin 4 → ℤ) : ℤ :=
  (u 0 * v 1 + u 1 * v 0) - 2 * (u 2 * v 2) - T * (u 2 * v 3 + u 3 * v 2)
    - 2 * M * (u 3 * v 3)

/-- The determinant of the Hermitian matrix `!![a, b; conj b, c]` with
`b = x + y ω`, namely `ac - N(b) = ac - (x² + T·xy + M·y²)`. -/
def hermDet (T M a c x y : ℤ) : ℤ := a * c - (x ^ 2 + T * x * y + M * y ^ 2)





/-- The Gram matrix of `bil` in the four basis vectors
(the two diagonal matrix units and the off-diagonal generators `1`, `ω`). -/
def gramMatrix (T M : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => bil T M (Pi.single i 1) (Pi.single j 1)



/-- The trace `T = Tr ω`: `1` if `d ≡ 1 [ZMOD 4]` (`ω = (1+√d)/2`), else `0`. -/
def omegaTrace (d : ℤ) : ℤ := if d % 4 = 1 then 1 else 0

/-- The norm `M = N ω`: `(1 - d)/4` if `d ≡ 1 [ZMOD 4]`, else `-d`. -/
def omegaNorm (d : ℤ) : ℤ := if d % 4 = 1 then (1 - d) / 4 else -d

/-- The fundamental discriminant `D_K`: `d` if `d ≡ 1 [ZMOD 4]`, else `4d`. -/
def fundamentalDisc (d : ℤ) : ℤ := if d % 4 = 1 then d else 4 * d




end HermitianBianchi


