-- Prove2me | Definitions.Def_Combinatorics_EllipticVerticalMoment
-- name    : Combinatorics_EllipticVerticalMoment
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:38:42.886127+00:00
-- url     : https://prove2.me/theorems/921e8361-5afb-4286-bc48-80823b7bda67
-- title:
--   Aether Catalog definitions — Combinatorics_EllipticVerticalMoment
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EllipticVerticalMoment`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EllipticVerticalMoment.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
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

namespace EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section QuadraticSums






end QuadraticSums

section Conic


end Conic

section Collisions





end Collisions

section VerticalMoment



/-- The diagonal of `F × F`. -/
private def diag (F : Type*) [Fintype F] [DecidableEq F] : Finset (F × F) :=
  univ.image fun x : F => ((x, x) : F × F)





end VerticalMoment

end EllipticModCount


