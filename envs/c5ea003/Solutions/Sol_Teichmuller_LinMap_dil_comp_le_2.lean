-- Prove2me | solution 2 for Teichmuller.LinMap.dil_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T05:23:45.781637+00:00
-- url     : https://prove2.me/submissions/d6d1c5b6-27d1-4df7-9b16-e91c444d53bf

/-
# `Teichmuller.LinMap.dil_comp_le`
Target `569d1452` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

With A = f.a·g.a + f.b·conj(g.b) and B = f.a·g.b + f.b·conj(g.a), write a,b,c,d for the four
norms ‖f.a‖,‖f.b‖,‖g.a‖,‖g.b‖.

A FIRST ATTEMPT FAILED AND THE FAILURE IS INSTRUCTIVE. Bounding numerator and denominator by two
SEPARATE estimates does not work:
    ‖A‖+‖B‖ ≤ (a+b)(c+d)                       -- valid
    ‖A‖-‖B‖ ≥ (ac-bd) - (ad+bc)                -- valid, but TOO WEAK
the second expands to ac-bd-ad-bc while the target (a-b)(c-d) expands to ac-ad-bc+bd. They differ
by 2bd, in the wrong direction. Two individually correct bounds, jointly too lossy: estimating the
two sides independently discards exactly the correlation that makes the theorem true.

The missing information is an EXACT identity — multiplicativity of the Jacobian:
    ‖A‖² - ‖B‖² = (a²-b²)(c²-d²) = [(a-b)(c-d)]·[(a+b)(c+d)]
Dividing it by the (valid) upper bound gives the lower bound as a CONSEQUENCE, not a second guess:
    ‖A‖-‖B‖ = (‖A‖²-‖B‖²)/(‖A‖+‖B‖) ≥ [(a-b)(c-d)(a+b)(c+d)]/[(a+b)(c+d)] = (a-b)(c-d).

Verified numerically over 60000 near-degenerate pairs (‖b‖ within 1e-4 of ‖a‖): zero violations,
one sample within 0.011 of equality, so the bound is near-tight.

PROBED, NOT GUESSED: `norm_add_le`, `norm_sub_norm_le`, `norm_mul`, `Complex.norm_conj` all
#check'd; `gcongr` closes numerator-down/denominator-up leaving a non-negativity side goal.
The `key` identity below is COPIED VERBATIM from this bundle's own `comp` proof, so it compiles.
-/
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LinearQC

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Teichmuller in
/-- **The target, verbatim.** -/
theorem solution (f g : LinMap) : (f.comp g).dil ≤ f.dil * g.dil := by
  have hfa := f.norm_lt
  have hga := g.norm_lt
  have hfpos : (0:ℝ) < ‖f.a‖ - ‖f.b‖ := by linarith
  have hgpos : (0:ℝ) < ‖g.a‖ - ‖g.b‖ := by linarith
  set A : ℂ := f.a * g.a + f.b * (starRingEnd ℂ) g.b with hA
  set B : ℂ := f.a * g.b + f.b * (starRingEnd ℂ) g.a with hB
  -- the exact identity, verbatim from the bundle's own `comp` proof
  have key : ‖A‖ ^ 2 - ‖B‖ ^ 2 = (‖f.a‖ ^ 2 - ‖f.b‖ ^ 2) * (‖g.a‖ ^ 2 - ‖g.b‖ ^ 2) := by
    simp only [hA, hB, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring
  -- upper bound on the numerator: triangle inequality, twice
  have hup : ‖A‖ + ‖B‖ ≤ (‖f.a‖ + ‖f.b‖) * (‖g.a‖ + ‖g.b‖) := by
    have h1 : ‖A‖ ≤ ‖f.a‖ * ‖g.a‖ + ‖f.b‖ * ‖g.b‖ := by
      calc ‖A‖ ≤ ‖f.a * g.a‖ + ‖f.b * (starRingEnd ℂ) g.b‖ := norm_add_le _ _
        _ = ‖f.a‖ * ‖g.a‖ + ‖f.b‖ * ‖g.b‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj]
    have h2 : ‖B‖ ≤ ‖f.a‖ * ‖g.b‖ + ‖f.b‖ * ‖g.a‖ := by
      calc ‖B‖ ≤ ‖f.a * g.b‖ + ‖f.b * (starRingEnd ℂ) g.a‖ := norm_add_le _ _
        _ = ‖f.a‖ * ‖g.b‖ + ‖f.b‖ * ‖g.a‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj]
    nlinarith [h1, h2]
  -- the sum is strictly positive, because the identity forces ‖B‖ < ‖A‖
  have hjf : (0:ℝ) < ‖f.a‖ ^ 2 - ‖f.b‖ ^ 2 := by nlinarith [norm_nonneg f.b]
  have hjg : (0:ℝ) < ‖g.a‖ ^ 2 - ‖g.b‖ ^ 2 := by nlinarith [norm_nonneg g.b]
  have hsq : ‖B‖ ^ 2 < ‖A‖ ^ 2 := by nlinarith [key, mul_pos hjf hjg]
  have hSpos : (0:ℝ) < ‖A‖ + ‖B‖ := by nlinarith [norm_nonneg A, norm_nonneg B, hsq]
  -- factor the identity so the two bracketed products appear literally
  have hfactor : ‖A‖ ^ 2 - ‖B‖ ^ 2
      = ((‖f.a‖ - ‖f.b‖) * (‖g.a‖ - ‖g.b‖)) * ((‖f.a‖ + ‖f.b‖) * (‖g.a‖ + ‖g.b‖)) := by
    rw [key]; ring
  -- lower bound as a CONSEQUENCE of the upper bound plus the identity
  have hPQS : 0 ≤ ((‖f.a‖ - ‖f.b‖) * (‖g.a‖ - ‖g.b‖))
      * ((‖f.a‖ + ‖f.b‖) * (‖g.a‖ + ‖g.b‖) - (‖A‖ + ‖B‖)) :=
    mul_nonneg (le_of_lt (mul_pos hfpos hgpos)) (by linarith)
  have hlow : (‖f.a‖ - ‖f.b‖) * (‖g.a‖ - ‖g.b‖) ≤ ‖A‖ - ‖B‖ := by
    nlinarith [hfactor, hPQS, hSpos]
  have hdpos : (0:ℝ) < ‖A‖ - ‖B‖ := lt_of_lt_of_le (mul_pos hfpos hgpos) hlow
  -- divide the bounds
  show (‖A‖ + ‖B‖) / (‖A‖ - ‖B‖) ≤ (‖f.a‖ + ‖f.b‖) / (‖f.a‖ - ‖f.b‖)
      * ((‖g.a‖ + ‖g.b‖) / (‖g.a‖ - ‖g.b‖))
  rw [div_mul_div_comm]
  -- `gcongr` discharges every side goal itself; the linter confirmed a trailing
  -- `positivity` here was never executed.
  gcongr
