-- Prove2me | Theorems.Thm_EllipticModCount_sum_char_quadratic
-- name    : EllipticModCount.sum_char_quadratic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:13:00.525789+00:00
-- url     : https://prove2.me/theorems/69b7d63d-2f76-4dfa-acfb-2bb3ccf24a04
-- title:
--   The complete quadratic character sum of a quadratic polynomial.
-- statement:
--   **The complete quadratic character sum of a quadratic polynomial.**
--
--   ```lean
--   theorem EllipticModCount.sum_char_quadratic(hF : ringChar F ≠ 2) {α : F} (hα : α ≠ 0) (β γ : F) :
--       ∑ v : F, quadraticChar F (α * v ^ 2 + β * v + γ)
--         = if β ^ 2 - 4 * α * γ = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F α
--           else -quadraticChar F α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticVerticalMoment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticVerticalMoment.lean#L166

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

theorem EllipticModCount.sum_char_quadratic(hF : ringChar F ≠ 2) {α : F} (hα : α ≠ 0) (β γ : F) :
    ∑ v : F, quadraticChar F (α * v ^ 2 + β * v + γ)
      = if β ^ 2 - 4 * α * γ = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F α
        else -quadraticChar F α := by sorry
