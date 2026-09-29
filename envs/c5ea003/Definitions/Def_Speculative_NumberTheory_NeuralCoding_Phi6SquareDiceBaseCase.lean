-- Prove2me | Definitions.Def_Speculative_NumberTheory_NeuralCoding_Phi6SquareDiceBaseCase
-- name    : Speculative_NumberTheory_NeuralCoding_Phi6SquareDiceBaseCase
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:06.361024+00:00
-- url     : https://prove2.me/theorems/5a21a755-0d64-4218-b1bb-125613cdeb99
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_NeuralCoding_Phi6SquareDiceBaseCase
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.NeuralCoding.Phi6SquareDiceBaseCase`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/NeuralCoding/Phi6SquareDiceBaseCase.lean by skeleton subtraction
import Mathlib

/-!
# Cyclotomic dice: the explicit base-case witness `p = 2, q = 3, m = 6, n = 2`

This file formalizes a single, fully explicit *admissible instance* of the cyclotomic
"dice transfer" construction.  The combinatorial object behind the algebra is a pair of
weighted dice whose generating polynomials multiply to the product of two consecutive-face
dice generating polynomials.

We work entirely over `Polynomial ℤ` (with auxiliary natural-coefficient polynomials over
`Polynomial ℕ` used only to certify coefficient nonnegativity).

The witness is built from the sixth cyclotomic polynomial `Φ₆ = X² - X + 1`.  Writing
`S N = X + X² + ⋯ + X^N` for the generating polynomial of a fair `N`-faced die, we prove:

* `phi6_mul_P36 : Phi6 * P36 = S 36`,
* `Q4_eq_phi6_mul_S4 : Q4 = Phi6 * S 4`,
* `product_identity : P36 * Q4 = S 36 * S 4`,
* `eval_P36_one : eval 1 P36 = 36` and `eval_Q4_one : eval 1 Q4 = 4`,
* coefficient nonnegativity of both `P36` and `Q4`.

Together these certify that the weighted dice with generating polynomials `P36` and `Q4`
have nonnegative integer face weights summing to `36` and `4` respectively, and reproduce
the product `S 36 * S 4` of two fair-dice generating polynomials.
-/

namespace Phi6SquareDiceBaseCase

open Polynomial Finset

/-- Generating polynomial of a fair `N`-faced die: `X + X² + ⋯ + X^N`. -/
noncomputable def S (N : ℕ) : Polynomial ℤ := ∑ i ∈ Finset.range N, X ^ (i + 1)

/-- The sixth cyclotomic polynomial `Φ₆ = X² - X + 1`. -/
noncomputable def Phi6 : Polynomial ℤ := X ^ 2 - X + 1

/-- The `j`-th natural-coefficient block: `X^{6j+1} + 2 X^{6j+2} + 2 X^{6j+3} + X^{6j+4}`. -/
noncomputable def blockNat (j : ℕ) : Polynomial ℕ :=
  X ^ (6 * j + 1) + C 2 * X ^ (6 * j + 2) + C 2 * X ^ (6 * j + 3) + X ^ (6 * j + 4)

/-- Natural-coefficient generating polynomial of the first weighted die. -/
noncomputable def P36Nat : Polynomial ℕ := ∑ j ∈ Finset.range 6, blockNat j

/-- The first weighted die's generating polynomial, over `ℤ`. -/
noncomputable def P36 : Polynomial ℤ := P36Nat.map (Nat.castRingHom ℤ)

/-- Natural-coefficient generating polynomial of the second weighted die. -/
noncomputable def Q4Nat : Polynomial ℕ := X + X ^ 3 + X ^ 4 + X ^ 6

/-- The second weighted die's generating polynomial, over `ℤ`. -/
noncomputable def Q4 : Polynomial ℤ := Q4Nat.map (Nat.castRingHom ℤ)

/-- Coefficientwise nonnegativity of an integer polynomial. -/
def CoeffNonneg (P : Polynomial ℤ) : Prop := ∀ k, 0 ≤ P.coeff k









end Phi6SquareDiceBaseCase


