-- Prove2me | solution 1 for RLHF.exp_sample_uniqueness_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:37:23.554971+00:00
-- url     : https://prove2.me/submissions/33af721c-1151-4c25-a2fd-d8da6fe9742e

-- Sol generated from NumberTheory/RLHFChebyshevSystem.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPronySampling
import Theorems.Thm_RLHF_expPoly_eq_zero_of_zeros

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
theorem solution{n : ℕ} {v : Fin n → ℝ} (hv : StrictMono v)
    {t : Fin n → ℝ} (ht : StrictMono t) {a b : Fin n → ℝ}
    (h : ∀ i, ∑ j, a j * Real.exp (v j * t i) = ∑ j, b j * Real.exp (v j * t i)) :
    a = b := by
  have hzero : ∀ i, ∑ j, (a j - b j) * Real.exp (v j * t i) = 0 := by
    intro i
    have hsplit : ∑ j, (a j - b j) * Real.exp (v j * t i)
        = (∑ j, a j * Real.exp (v j * t i)) - ∑ j, b j * Real.exp (v j * t i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsplit, h i, sub_self]
  have := expPoly_eq_zero_of_zeros n v (fun j => a j - b j) t hv ht hzero
  funext j
  have hj := this j
  simpa [sub_eq_zero] using hj
