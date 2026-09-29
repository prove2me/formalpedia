-- Prove2me | Theorems.Thm_EllipticModCount_rootSet_eq_of_two_roots
-- name    : EllipticModCount.rootSet_eq_of_two_roots
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:12:55.782753+00:00
-- url     : https://prove2.me/theorems/938ab71f-cb5d-4076-952a-5c1778b5be7e
-- title:
--   Two distinct roots of a nonsingular cubic force a third one, distinct from both.
-- statement:
--   Two distinct roots of a nonsingular cubic force a third one, distinct from both.
--
--   ```lean
--   theorem EllipticModCount.rootSet_eq_of_two_roots(hd : disc a b ≠ 0)
--       (hr : wRHS a b r = 0) (hs : wRHS a b s = 0) (hrs : r ≠ s) :
--       rootSet a b = {r, s, -(r + s)} ∧ (rootSet a b).card = 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticPointCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticPointCount.lean#L163

-- Thm stub generated from Combinatorics/EllipticPointCount.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
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

open EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]




















variable {a b r s : F}

theorem EllipticModCount.rootSet_eq_of_two_roots(hd : disc a b ≠ 0)
    (hr : wRHS a b r = 0) (hs : wRHS a b s = 0) (hrs : r ≠ s) :
    rootSet a b = {r, s, -(r + s)} ∧ (rootSet a b).card = 3 := by sorry
