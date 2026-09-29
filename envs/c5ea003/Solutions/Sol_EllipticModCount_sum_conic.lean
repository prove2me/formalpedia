-- Prove2me | solution 1 for EllipticModCount.sum_conic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:59:10.514259+00:00
-- url     : https://prove2.me/submissions/67774871-4d7d-4359-9c2e-87bf73a2c9bf

-- Sol generated from Combinatorics/EllipticVerticalMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Definitions.Def_Combinatorics_EllipticVerticalMoment
import Theorems.Thm_EllipticModCount_sum_char_quadratic
import Theorems.Thm_EllipticModCount_sum_ite_quadratic_root
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



























open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (h3 : (3 : F) ≠ 0) (c : F) :
    ∑ x : F, ∑ y : F, (if x ^ 2 + x * y + y ^ 2 = c then (1 : ℤ) else 0)
      = (Fintype.card F : ℤ)
        + (if c = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F (-3)
           else -quadraticChar F (-3)) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    have he : (4 : F) = 2 * 2 := by norm_num
    rw [he]
    exact mul_ne_zero h2 h2
  have hn3 : (-3 : F) ≠ 0 := neg_ne_zero.mpr h3
  have hinner : ∀ x : F, ∑ y : F, (if x ^ 2 + x * y + y ^ 2 = c then (1 : ℤ) else 0)
      = quadraticChar F (-3 * x ^ 2 + 0 * x + 4 * c) + 1 := by
    intro x
    have hcond : ∀ y : F, (x ^ 2 + x * y + y ^ 2 = c) ↔ (y ^ 2 + x * y + (x ^ 2 - c) = 0) := by
      intro y
      constructor
      · intro h
        linear_combination h
      · intro h
        linear_combination h
    rw [Finset.sum_congr rfl fun y _ => if_congr (hcond y) rfl rfl,
      sum_ite_quadratic_root hF x (x ^ 2 - c)]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun x _ => hinner x, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, sum_char_quadratic hF hn3 0 (4 * c)]
  have hdisc : ((0 : F) ^ 2 - 4 * (-3) * (4 * c) = 0) ↔ (c = 0) := by
    constructor
    · intro h
      have h48 : (48 : F) * c = 0 := by linear_combination h
      rcases mul_eq_zero.mp h48 with h' | h'
      · exfalso
        apply h3
        have h16 : (48 : F) = 16 * 3 := by norm_num
        rw [h16] at h'
        rcases mul_eq_zero.mp h' with h'' | h''
        · exfalso
          apply h4
          have : (16 : F) = 4 * 4 := by norm_num
          rw [this] at h''
          rcases mul_eq_zero.mp h'' with h3' | h3' <;> exact h3'
        · exact h''
      · exact h'
    · intro h
      rw [h]
      ring
  by_cases hc : c = 0
  · rw [if_pos hc, if_pos (hdisc.mpr hc)]
    ring
  · rw [if_neg hc, if_neg (fun hx => hc (hdisc.mp hx))]
    ring
