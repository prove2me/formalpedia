-- Prove2me | solution 1 for RLHF.hasDerivAt_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:32:26.58999+00:00
-- url     : https://prove2.me/submissions/47e14cea-0e8f-4fbe-a6be-f06b6f488658

-- Sol generated from NumberTheory/RLHFChebyshevSystem.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPronySampling

/-!
# Exponential sums form a Chebyshev system: `n` arbitrary temperatures suffice

`RLHF.exp_sample_uniqueness` recovers the masses on `n` known reward levels from the
partition function at `n` *arithmetically spaced* inverse temperatures, by a Vandermonde
determinant.  This file removes the arithmetic-grid hypothesis: **any** `n` distinct
temperatures do.

The engine is the classical Descartes/Chebyshev fact, proved here by induction on the number
of exponents with Rolle's theorem supplying the inductive step:

* `RLHF.expPoly_eq_zero_of_zeros` — a real exponential polynomial `∑_{j<n} c_j e^{v_j x}`
  with `n` strictly increasing exponents that vanishes at `n` distinct points has all
  coefficients zero.  (Equivalently: a nonzero exponential polynomial with `n` exponents has
  at most `n − 1` real zeros.)
* `RLHF.exp_sample_uniqueness_general` — consequently two mass vectors on the same `n` known
  distinct levels are equal as soon as their exponential sums agree at `n` distinct
  temperatures.
* `RLHF.spectral_rigidity_sampled_general` — the RLHF audit statement: with `n` known
  candidate reward levels, `n` arbitrary distinct inverse temperatures determine the reward
  spectrum.

Combined with `RLHF.prony_three_samples_insufficient_spectra`, the picture for the sampling
question is complete in the known-level case, and provably different when the levels are
unknown.
-/

open RLHF

open Finset






open RLHF in
theorem solution{n : ℕ} (c w : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun x => ∑ j, c j * Real.exp (w j * x))
      (∑ j, c j * w j * Real.exp (w j * x)) x := by
  have h : ∀ j ∈ (univ : Finset (Fin n)),
      HasDerivAt (fun x => c j * Real.exp (w j * x)) (c j * w j * Real.exp (w j * x)) x := by
    intro j _
    have h1 : HasDerivAt (fun x : ℝ => w j * x) (w j) x := by
      simpa using (hasDerivAt_id x).const_mul (w j)
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (w j * x)) (Real.exp (w j * x) * w j) x := h1.exp
    have h3 := h2.const_mul (c j)
    convert h3 using 1
    ring
  have hs := HasDerivAt.sum h
  have hfun : (∑ j ∈ (univ : Finset (Fin n)), fun x => c j * Real.exp (w j * x))
      = fun x => ∑ j, c j * Real.exp (w j * x) := by
    funext x
    simp [Finset.sum_apply]
  rw [hfun] at hs
  exact hs
