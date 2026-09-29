-- Prove2me | solution 1 for EllipticModCount.card_affineLocus
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:44:58.076867+00:00
-- url     : https://prove2.me/submissions/3c8ff92b-2382-4ac3-b7d4-c87f49627f58

-- Sol generated from Combinatorics/EllipticPointCount.lean
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









/-- The number of square roots of `c` in `F`, as a `Finset` cardinality. -/
theorem card_sqrt_filter (hF : ringChar F ≠ 2) (c : F) :
    ((univ.filter fun y : F => y ^ 2 = c).card : ℤ) = quadraticChar F c + 1 := by
  have h := quadraticChar_card_sqrts hF c
  rw [← h]
  congr 2
  rw [Set.toFinset_setOf]











variable {a b r s : F}
















variable {a b d : F}











open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (a b : F) :
    ((affineLocus a b).card : ℤ) = (Fintype.card F : ℤ) + charSum a b := by
  have key : ∀ x : F,
      ((univ.filter fun y : F => y ^ 2 = wRHS a b x).card : ℤ)
        = quadraticChar F (wRHS a b x) + 1 := fun x => card_sqrt_filter hF _
  have h2 : (affineLocus a b).card
      = ∑ x : F, (univ.filter fun y : F => y ^ 2 = wRHS a b x).card := by
    rw [affineLocus, Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
  rw [h2]
  push_cast
  rw [Finset.sum_congr rfl fun x _ => key x]
  rw [Finset.sum_add_distrib]
  simp [charSum, Finset.card_univ, add_comm]
