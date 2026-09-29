-- Prove2me | Definitions.Def_Algebra_MatrixEncoding
-- name    : Algebra_MatrixEncoding
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:22:01.361282+00:00
-- url     : https://prove2.me/theorems/0f883d23-3db9-422d-bb73-8b77c15dbcbb
-- title:
--   Aether Catalog definitions — Algebra_MatrixEncoding
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.MatrixEncoding`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/MatrixEncoding.lean by skeleton subtraction
import Mathlib

/-!
# Matrix Encoding of Continued Fraction Digits

This file formalizes the correspondence between continued fraction digit words
and products of matrices in SL₂(ℤ). Each partial quotient `a` corresponds to
the matrix `[[0, 1], [1, a]]`, and a digit word `[a₁, …, aₖ]` maps to the
product of these matrices. We prove that for positive digit words, the
determinant of the word matrix alternates between +1 and -1 (specifically,
`det(wordMatrix w) = (-1)^(length w)`).

## Main definitions

- `cfMatrix a` : the 2×2 matrix `[[0, 1], [1, a]]` for digit `a`
- `wordMatrix w` : the product of `cfMatrix` over a digit word `w`

## Main results

- `cfMatrix_det` : `det (cfMatrix a) = -1`
- `wordMatrix_det` : `det (wordMatrix w) = (-1)^(length w)`
- `wordMatrix_append` : `wordMatrix (u ++ v) = wordMatrix u * wordMatrix v`
-/

namespace ContinuedFractions

open Matrix

/-- The continued fraction matrix for a single digit `a`:
    `[[0, 1], [1, a]]`. This encodes the Möbius transformation
    `x ↦ 1/(a + x)` which is the inverse branch of the Gauss map
    corresponding to digit `a`. -/
def cfMatrix (a : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, a]

/-- The word matrix for a sequence of digits: the product of individual
    digit matrices. For `w = [a₁, …, aₖ]`, this is
    `cfMatrix a₁ * cfMatrix a₂ * ⋯ * cfMatrix aₖ`.
    The empty word gives the identity matrix. -/
def wordMatrix : List ℤ → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | a :: w => cfMatrix a * wordMatrix w

/-
The determinant of a single digit matrix is -1.
-/



/-
Word matrix respects list append: `wordMatrix (u ++ v) = wordMatrix u * wordMatrix v`.
-/

/-
The determinant of a word matrix is `(-1)^(length w)`.
    This is the key algebraic fact: continued fraction matrix products
    have determinant ±1, alternating with word length.
-/

/-
For a single-digit word, the word matrix equals the digit matrix.
-/

/-
The (0,0) entry of `cfMatrix a` is 0.
-/

/-
The (0,1) entry of `cfMatrix a` is 1.
-/

/-
The (1,0) entry of `cfMatrix a` is 1.
-/

/-
The (1,1) entry of `cfMatrix a` is `a`.
-/

/-
Word matrices of positive digit lists are invertible (have unit determinant up to sign).
-/

/-
The product of two word matrices corresponds to concatenation.
-/

end ContinuedFractions


