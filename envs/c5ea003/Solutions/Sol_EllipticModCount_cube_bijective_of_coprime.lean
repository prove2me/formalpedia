-- Prove2me | solution 1 for EllipticModCount.cube_bijective_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:02:41.28967+00:00
-- url     : https://prove2.me/submissions/1c567bd8-0123-4e24-abba-774657b864c0

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




















variable {a b r s : F}
















variable {a b d : F}











open EllipticModCount in
theorem solution(h : Nat.Coprime (Fintype.card F - 1) 3) :
    Function.Bijective fun x : F => x ^ 3 := by
  have hinj : Function.Injective fun x : F => x ^ 3 := by
    have hu : Function.Bijective fun u : Fˣ => u ^ 3 := by
      apply Nat.Coprime.pow_left_bijective
      simpa [Nat.card_eq_fintype_card, Fintype.card_units] using h
    intro x y hxy
    simp only at hxy
    by_cases hy : y = 0
    · subst hy
      have h0 : x ^ 3 = 0 := by simpa using hxy
      exact pow_eq_zero_iff (by norm_num) |>.mp h0
    · have hx : x ≠ 0 := by
        intro hx
        apply hy
        rw [hx] at hxy
        have h0 : y ^ 3 = 0 := by simpa using hxy.symm
        exact pow_eq_zero_iff (by norm_num) |>.mp h0
      have : (Units.mk0 x hx) ^ 3 = (Units.mk0 y hy) ^ 3 := by
        ext
        simpa using hxy
      have := hu.injective this
      simpa using congrArg (Units.val) this
  exact Finite.injective_iff_bijective.mp hinj
