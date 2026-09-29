-- Prove2me | solution 1 for MordellDenominators.exists_reduction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:25:27.251592+00:00
-- url     : https://prove2.me/submissions/ad0242a0-e0f3-4f28-81e5-1a1ef3a445a6

-- Sol generated from Cryptography/MordellDenominators/Reduction.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_curve_integral_model
import Theorems.Thm_MordellDenominators_exists_den_param

/-!
# Reduction modulo `ℓ` and the meaning of a denominator prime

This file explains *why* good primes can occur in denominators.  Writing a
rational point of `E_N : y² = x³ + N` as `x = a/e²`, `y = b/e³` we obtain the
integral model `b² = a³ + N e⁶` (`curve_integral_model`, proved in
`Basic.lean`), and then a clean dichotomy for every prime
`ℓ`:

* if `ℓ ∤ x.den`, the point **reduces to an affine point** of `E_N(𝔽_ℓ)`
  (`MordellDenominators.exists_reduction`);
* if `ℓ ∣ x.den`, the point has **no affine reduction** — it reduces to the
  point at infinity `O` (`MordellDenominators.no_affine_reduction`).

Consequently a prime — good or bad — occurs in a denominator exactly when the
point falls into the kernel of reduction at that prime
(`MordellDenominators.dvd_den_iff_no_affine_reduction`).  Nothing in this
mechanism refers to the discriminant, which is the structural reason why the
"only bad primes" conjecture had to fail.
-/

open MordellDenominators





open MordellDenominators in
theorem solution{N : ℤ} {x y : ℚ} (h : OnCurve N x y) {l : ℕ}
    (hl : l.Prime) (hnd : ¬ l ∣ x.den) :
    ∃ X Y : ZMod l, Y ^ 2 = X ^ 3 + (N : ZMod l) ∧
      X * (x.den : ZMod l) = (x.num : ZMod l) ∧
      Y * (y.den : ZMod l) = (y.num : ZMod l) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨e, he0, hxe, hye⟩ := exists_den_param h
  have hle : ¬ (l ∣ e) := by
    intro hcon
    exact hnd (by rw [hxe]; exact Dvd.dvd.trans hcon (dvd_pow_self e (by norm_num)))
  have hez : (e : ZMod l) ≠ 0 := by
    intro hcon
    exact hle ((ZMod.natCast_eq_zero_iff e l).mp hcon)
  have hmodel := curve_integral_model h hxe hye
  have hmodelZ : ((y.num : ZMod l)) ^ 2 =
      ((x.num : ZMod l)) ^ 3 + (N : ZMod l) * ((e : ZMod l)) ^ 6 := by
    have hcast : ((y.num ^ 2 : ℤ) : ZMod l) = ((x.num ^ 3 + N * (e : ℤ) ^ 6 : ℤ) : ZMod l) := by
      rw [hmodel]
    push_cast at hcast
    exact hcast
  refine ⟨(x.num : ZMod l) * ((e : ZMod l) ^ 2)⁻¹,
    (y.num : ZMod l) * ((e : ZMod l) ^ 3)⁻¹, ?_, ?_, ?_⟩
  · field_simp
    linear_combination hmodelZ
  · rw [hxe]
    push_cast
    field_simp
  · rw [hye]
    push_cast
    field_simp
