-- Prove2me | solution 1 for EMLSpecialFunctions.hypergeometricCoeff_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:02:15.448666+00:00
-- url     : https://prove2.me/submissions/000d1dcc-6c98-4f1f-90b4-ae1637cc802b

-- Sol generated from Applications/EML/HypergeometricEquation.lean
import Mathlib
import Definitions.Def_Applications_EML_HypergeometricEquation

/-!
# Gauss's hypergeometric differential equation

This file formalizes the coefficient sequence of the Gauss hypergeometric series
`₂F₁(a,b;c;z)` and proves, purely formally, that it is annihilated coefficient by
coefficient by Gauss's differential operator

`z(1-z)y'' + (c-(a+b+1)z)y' - ab y`.

Working with coefficient sequences makes the result independent of analytic
convergence questions and captures the algebraic core of the differential equation.
-/

open EMLSpecialFunctions



/-- The defining hypergeometric recurrence, in denominator-free form. -/
theorem hypergeometricCoeff_recurrence (a b c : ℂ) (n : ℕ)
    (hc : c + n ≠ 0) :
    (n + 1) * (c + n) * hypergeometricCoeff a b c (n + 1) =
      (a + n) * (b + n) * hypergeometricCoeff a b c n := by
  simp [hypergeometricCoeff]
  field_simp [hc]






open EMLSpecialFunctions in
theorem solution(a b c : ℂ) (u : ℕ → ℂ)
    (u0 : u 0 = 1)
    (hu : ∀ n : ℕ, (n + 1) * (c + n) * u (n + 1) =
      (a + n) * (b + n) * u n)
    (hc : ∀ n : ℕ, c + n ≠ 0) :
    u = hypergeometricCoeff a b c := by
  funext n
  induction n with
  | zero => exact u0
  | succ n ih =>
    have h1 := hu n
    have h2 := hypergeometricCoeff_recurrence a b c n (hc n)
    rw [ih] at h1
    have hfactor : (n + 1) * (c + n) ≠ 0 := by
      apply mul_ne_zero
      · exact Nat.cast_add_one_ne_zero n
      · exact hc n
    exact mul_right_injective₀ hfactor (h1.trans h2.symm)
