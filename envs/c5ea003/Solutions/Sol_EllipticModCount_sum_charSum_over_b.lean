-- Prove2me | solution 1 for EllipticModCount.sum_charSum_over_b
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:10:59.359405+00:00
-- url     : https://prove2.me/submissions/380288ab-b0b5-498e-9f43-f166dca30700

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








omit [Field F] [DecidableEq F] in
/-- Reindexing a character sum along a bijection. -/
private lemma sum_comp_bijective {e : F → F} (he : Function.Bijective e) (g : F → ℤ) :
    ∑ x : F, g (e x) = ∑ x : F, g x :=
  Fintype.sum_bijective e he _ _ fun _ => rfl








variable {a b d : F}











open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (a : F) : ∑ b : F, charSum a b = 0 := by
  have hswap : ∑ b : F, charSum a b = ∑ x : F, ∑ b : F, quadraticChar F (wRHS a b x) :=
    Finset.sum_comm
  rw [hswap]
  refine Finset.sum_eq_zero fun x _ => ?_
  have : ∀ b : F, quadraticChar F (wRHS a b x) = quadraticChar F ((x ^ 3 + a * x) + b) :=
    fun _ => rfl
  have hb : Function.Bijective (fun b : F => (x ^ 3 + a * x) + b) := by
    constructor
    · intro u v h
      simpa using h
    · intro v
      exact ⟨v - (x ^ 3 + a * x), by ring⟩
  rw [Finset.sum_congr rfl fun b _ => this b]
  exact (sum_comp_bijective hb (fun u => quadraticChar F u)).trans (quadraticChar_sum_zero hF)
