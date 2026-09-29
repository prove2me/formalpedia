-- Prove2me | Definitions.Def_MachineLearning_CollatzSpectralGap
-- name    : MachineLearning_CollatzSpectralGap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:05.272985+00:00
-- url     : https://prove2.me/theorems/88680d28-8346-4074-8e56-ccee6ef0459e
-- title:
--   Aether Catalog definitions — MachineLearning_CollatzSpectralGap
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CollatzSpectralGap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CollatzSpectralGap.lean by skeleton subtraction
import Mathlib

/-!
# A Fourier obstruction to the proposed Collatz spectral gap

For a finite cutoff, the Collatz exponential sum is continuous in frequency and
has value `N` at frequency zero. Since irrational frequencies are dense, its
norm is arbitrarily close to `N` at irrational frequencies. Consequently, no
uniform bound smaller than `N`—in particular no bound smaller than `√N` when
`N > 1`—can hold at every irrational frequency.
-/

namespace CollatzSpectralGap

open scoped ComplexConjugate
open Filter Set

/-- The usual unaccelerated Collatz map on natural numbers. -/
def collatz (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

/-- The finite Collatz exponential sum with cutoff `N`, indexed by `1, …, N`. -/
noncomputable def collatzFourier (N : ℕ) (ω : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N,
    Complex.exp
      (2 * Real.pi * Complex.I * (ω : ℂ) *
        ((collatz (k + 1) : ℂ) / (k + 1 : ℂ)))








end CollatzSpectralGap


