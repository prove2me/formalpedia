-- Prove2me | Definitions.Def_Combinatorics_EllipticPointCount
-- name    : Combinatorics_EllipticPointCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:34:52.878968+00:00
-- url     : https://prove2.me/theorems/5541b8bf-2740-46a8-9903-35e150961f27
-- title:
--   Aether Catalog definitions — Combinatorics_EllipticPointCount
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EllipticPointCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EllipticPointCount.lean by skeleton subtraction
import Mathlib
/-
# Exact point counting and modular invariants for short Weierstrass curves

For a finite field `F` of odd characteristic and parameters `a b : F` we study the
affine locus of the short Weierstrass equation `y^2 = x^3 + a*x + b` together with
one point at infinity.  Everything is done by *elementary counting*: the basic tool
is the quadratic character `quadraticChar F`, which counts square roots.

Main results:

* `EllipticModCount.card_affineLocus` : the affine point count equals `#F + S(a,b)`
  where `S(a,b) = ∑ x, χ(x^3+a*x+b)`.
* `EllipticModCount.frobTrace_eq_neg_charSum` : the trace of Frobenius is `-S(a,b)`.
* `EllipticModCount.two_dvd_cardPoints_iff` : (**2-torsion criterion**) for a
  nonsingular curve the point count is even iff the cubic has a root in `F`.
* `EllipticModCount.rootSet_card_cases` : for a nonsingular curve the cubic has
  exactly `0`, `1` or `3` roots — never `2`.
* `EllipticModCount.cardPoints_eq_of_cube_bijective` : if cubing is a bijection
  (e.g. `p % 3 = 2`) then `y^2 = x^3 + b` has exactly `#F + 1` points.
* `EllipticModCount.cardPoints_eq_of_neg_one_nonsquare` : if `-1` is a nonsquare
  (e.g. `p % 4 = 3`) then `y^2 = x^3 + a*x` has exactly `#F + 1` points.
* `EllipticModCount.frobTrace_twist` : quadratic twisting negates the trace.
* `EllipticModCount.sum_frobTrace_eq_zero` : the trace averages to `0` over the
  family `b ↦ (a,b)`, and over the whole family `(a,b)`.
-/

namespace EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The right-hand side `x^3 + a*x + b` of a short Weierstrass equation. -/
def wRHS (a b x : F) : F := x ^ 3 + a * x + b

/-- The affine solution set of `y^2 = x^3 + a*x + b`. -/
def affineLocus (a b : F) : Finset (F × F) :=
  univ.filter fun P => P.2 ^ 2 = wRHS a b P.1

/-- The number of projective points: affine solutions together with the point at infinity. -/
def cardPoints (a b : F) : ℕ := (affineLocus a b).card + 1

/-- The trace of Frobenius `#F + 1 - #E(F)`. -/
def frobTrace (a b : F) : ℤ := (Fintype.card F : ℤ) + 1 - (cardPoints a b : ℤ)

/-- The character sum `∑ x, χ(x^3+a*x+b)`. -/
def charSum (a b : F) : ℤ := ∑ x : F, quadraticChar F (wRHS a b x)

/-- The set of roots of the cubic `x^3 + a*x + b`, i.e. the `x`-coordinates of 2-torsion. -/
def rootSet (a b : F) : Finset F := univ.filter fun x => wRHS a b x = 0

/-- The discriminant (up to sign and a constant) of `x^3 + a*x + b`. -/
def disc (a b : F) : F := 4 * a ^ 3 + 27 * b ^ 2

section Counting






end Counting

section Parity



end Parity

section RootCount

variable {a b r s : F}






end RootCount

section Reindex


end Reindex

section Supersingular




end Supersingular

section Twist

variable {a b d : F}




end Twist

section Averages




end Averages

end EllipticModCount


