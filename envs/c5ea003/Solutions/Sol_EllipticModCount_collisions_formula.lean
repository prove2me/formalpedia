-- Prove2me | solution 1 for EllipticModCount.collisions_formula
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:01:09.124778+00:00
-- url     : https://prove2.me/submissions/8fbfca13-00c5-4276-9021-75620e21c208

-- Sol generated from Combinatorics/EllipticVerticalMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Definitions.Def_Combinatorics_EllipticVerticalMoment
import Theorems.Thm_EllipticModCount_sum_conic
import Theorems.Thm_EllipticModCount_sum_ite_sq
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












/-- The collision count as a double sum of indicators. -/
theorem collisions_eq_sum (a : F) :
    (collisions a : ℤ)
      = ∑ x : F, ∑ y : F, (if x ^ 3 + a * x = y ^ 3 + a * y then (1 : ℤ) else 0) := by
  rw [collisions, Finset.card_filter]
  push_cast
  exact Fintype.sum_prod_type'
    (fun x y : F => if x ^ 3 + a * x = y ^ 3 + a * y then (1 : ℤ) else 0)















open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (h3 : (3 : F) ≠ 0) (a : F) :
    (collisions a : ℤ) = (Fintype.card F : ℤ)
      + ((Fintype.card F : ℤ)
        + (if -a = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F (-3)
           else -quadraticChar F (-3)))
      - (quadraticChar F (-a / 3) + 1) := by
  have hsplit : ∀ x y : F, (if x ^ 3 + a * x = y ^ 3 + a * y then (1 : ℤ) else 0)
      = (if x = y then (1 : ℤ) else 0) + (if x ^ 2 + x * y + y ^ 2 = -a then (1 : ℤ) else 0)
        - (if x = y then (if x ^ 2 + x * y + y ^ 2 = -a then (1 : ℤ) else 0) else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg hxy, if_neg hxy]
      have hiff : (x ^ 3 + a * x = y ^ 3 + a * y) ↔ (x ^ 2 + x * y + y ^ 2 = -a) := by
        constructor
        · intro h
          have hfac : (x - y) * (x ^ 2 + x * y + y ^ 2 + a) = 0 := by linear_combination h
          rcases mul_eq_zero.mp hfac with h' | h'
          · exact absurd (by linear_combination h' : x = y) hxy
          · linear_combination h'
        · intro h
          linear_combination (x - y) * h
      rw [if_congr hiff rfl rfl]
      ring
  rw [collisions_eq_sum a]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsplit x y]
  have hexp : ∀ x : F, ∑ y : F,
      ((if x = y then (1 : ℤ) else 0) + (if x ^ 2 + x * y + y ^ 2 = -a then (1 : ℤ) else 0)
        - (if x = y then (if x ^ 2 + x * y + y ^ 2 = -a then (1 : ℤ) else 0) else 0))
      = 1 + (∑ y : F, (if x ^ 2 + x * y + y ^ 2 = -a then (1 : ℤ) else 0))
        - (if x ^ 2 + x * x + x ^ 2 = -a then (1 : ℤ) else 0) := by
    intro x
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq univ x (fun _ : F => (1 : ℤ)),
      Finset.sum_ite_eq univ x (fun y : F => if x ^ 2 + x * y + y ^ 2 = -a then (1 : ℤ) else 0)]
    simp only [mem_univ, if_true]
  rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sum_conic hF h3 (-a)]
  have hlast : ∑ x : F, (if x ^ 2 + x * x + x ^ 2 = -a then (1 : ℤ) else 0)
      = quadraticChar F (-a / 3) + 1 := by
    have hc : ∀ x : F, (x ^ 2 + x * x + x ^ 2 = -a) ↔ (x ^ 2 = -a / 3) := by
      intro x
      constructor
      · intro h
        field_simp
        linear_combination h
      · intro h
        field_simp at h
        linear_combination h
    rw [Finset.sum_congr rfl fun x _ => if_congr (hc x) rfl rfl, sum_ite_sq hF]
  rw [hlast]
