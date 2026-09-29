-- Prove2me | Theorems.Thm_EllipticModCount_collisions_formula
-- name    : EllipticModCount.collisions_formula
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:12:34.853677+00:00
-- url     : https://prove2.me/theorems/50c4eb2d-5b88-472b-9b5e-0659689812e5
-- title:
--   Exact collision count.
-- statement:
--   **Exact collision count.** `#{(x,y) : x^3+ax = y^3+ay} = 2q - 1 - χ(-3) - χ(-a/3)`
--   for `a ≠ 0`, and `2q - 1 + (q-1)χ(-3)` for `a = 0`.
--
--   ```lean
--   theorem EllipticModCount.collisions_formula(hF : ringChar F ≠ 2) (h3 : (3 : F) ≠ 0) (a : F) :
--       (collisions a : ℤ) = (Fintype.card F : ℤ)
--         + ((Fintype.card F : ℤ)
--           + (if -a = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F (-3)
--              else -quadraticChar F (-3)))
--         - (quadraticChar F (-a / 3) + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticVerticalMoment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticVerticalMoment.lean#L286

-- Thm stub generated from Combinatorics/EllipticVerticalMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Definitions.Def_Combinatorics_EllipticVerticalMoment
/-
# Quadratic character sums, conic counts, and the exact vertical second moment

This file completes the elementary toolkit for the family `y^2 = x^3 + a*x + b` over a
finite field `F` of characteristic `≠ 2, 3` by evaluating **every** quadratic character
sum of a quadratic polynomial, counting the points of the conic `x^2+x*y+y^2 = c`, and
deducing the **exact vertical second moment**

`∑_{b ∈ F} a(a,b)^2 = q^2 - q * (1 + χ(-3) + χ(-3a))`  for `a ≠ 0`,
`∑_{b ∈ F} a(0,b)^2 = q * (q-1) * (1 + χ(-3))`.

The second formula gives a second, independent proof that the family `y^2 = x^3 + b` is
supersingular exactly when `χ(-3) = -1`, i.e. when `q ≡ 2 (mod 3)`.

Main results:

* `EllipticModCount.sum_char_quadratic` : `∑_v χ(αv^2+βv+γ) = -χ(α)` unless the
  discriminant vanishes, in which case it is `(q-1)χ(α)`.
* `EllipticModCount.sum_conic` : the number of points of `x^2+xy+y^2 = c`.
* `EllipticModCount.collisions_eq` / `collisions_zero` : exact collision counts.
* `EllipticModCount.vertical_second_moment` / `vertical_second_moment_zero`.
* `EllipticModCount.vertical_second_moment_zero_eq_zero_iff` : supersingularity of the
  family `y^2 = x^3 + b` is *equivalent* to `χ(-3) = -1`.
-/

open EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem EllipticModCount.collisions_formula(hF : ringChar F ≠ 2) (h3 : (3 : F) ≠ 0) (a : F) :
    (collisions a : ℤ) = (Fintype.card F : ℤ)
      + ((Fintype.card F : ℤ)
        + (if -a = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F (-3)
           else -quadraticChar F (-3)))
      - (quadraticChar F (-a / 3) + 1) := by sorry
