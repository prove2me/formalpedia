-- Prove2me | solution 1 for EllipticModCount.charSum_twist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:54:07.352703+00:00
-- url     : https://prove2.me/submissions/5fcdbfc4-9f8c-4340-a330-c4a7066bf764

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
theorem solution(hd : quadraticChar F d = -1) (a b : F) :
    charSum (a * d ^ 2) (b * d ^ 3) = -charSum a b := by
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at hd
    exact absurd hd (by decide)
  have hbij : Function.Bijective fun u : F => d * u := by
    refine ⟨fun u v huv => by field_simp at huv; exact huv, fun v => ⟨d⁻¹ * v, by field_simp⟩⟩
  have hstep : ∀ u : F, quadraticChar F (d ^ 3 * wRHS a b u)
      = quadraticChar F (wRHS (a * d ^ 2) (b * d ^ 3) (d * u)) := by
    intro u
    congr 1
    rw [wRHS, wRHS]
    ring
  calc charSum (a * d ^ 2) (b * d ^ 3)
      = ∑ u : F, quadraticChar F (wRHS (a * d ^ 2) (b * d ^ 3) (d * u)) :=
        (sum_comp_bijective hbij (fun x => quadraticChar F (wRHS (a * d ^ 2) (b * d ^ 3) x))).symm
    _ = ∑ u : F, quadraticChar F (d ^ 3 * wRHS a b u) :=
        Finset.sum_congr rfl fun u _ => (hstep u).symm
    _ = ∑ u : F, (-1) * quadraticChar F (wRHS a b u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [map_mul, map_pow, hd]
        norm_num
    _ = -charSum a b := by rw [← Finset.mul_sum, neg_one_mul]; rfl
