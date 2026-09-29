-- Prove2me | Theorems.Thm_SpectralFreeWitness_chi_add_chi_neg
-- name    : SpectralFreeWitness.chi_add_chi_neg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:50:53.390883+00:00
-- url     : https://prove2.me/theorems/d7c706cf-00ba-443b-9c98-28474c0558f8
-- title:
--   Real form of a conjugate pair of character values.
-- statement:
--   Real form of a conjugate pair of character values.
--
--   ```lean
--   theorem SpectralFreeWitness.chi_add_chi_neg(r k : ℕ) (m : ℤ) :
--       chi r k m + chi r k (-m) = 2 * ((Real.cos (2 * π * ((k : ℝ) * (m : ℝ)) / r) : ℝ) : ℂ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/SpectralFreeWitnessWalk.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/SpectralFreeWitnessWalk.lean#L46

-- Thm stub generated from Speculative/AutoResearch/SpectralFreeWitnessWalk.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitnessWalk
/-
# The dyadic diffusion operator: heat kernel = return probability

`Algebra.SpectralFreeWitness` defines the heat-kernel value `p_n(e)` *spectrally*,
as `(1/r) ∑_k μ_k^n`.  This file shows that this spectral definition is the genuine
`n`-step return probability of the half-lazy lacunary dyadic random walk, by

* introducing the diffusion (transition) operator
  `W f (x) = f x / 2 + (∑_{t ≤ M} (f (x + 2^t) + f (x - 2^t))) / (4 (M+1))`
  acting on `r`-periodic functions on the cycle `Z/rZ` (realised as functions `ℤ → ℂ`),
* proving that the additive characters `χ_k (x) = e^{2πi k x / r}` are eigenvectors
  of `W` with eigenvalues exactly the `lazyEigen r M k` of the spectral file
  (`walkStep_chi`),
* proving the discrete Fourier expansion of the periodic delta function
  (`sum_chi`: character orthogonality on `Z/rZ`),
* concluding `W^[n] δ (0) = p_n(e)` (`walk_return_eq_heatReturn`), and hence the
  fully operational statement of heat-kernel order recovery
  (`walk_recovers_order`): the *measured* return probability of the diffusion,
  after `8 (M+1)^2` steps, determines the order `r` by a single rounding.

No `sorry`, no `native_decide`.
-/


open SpectralFreeWitness

open Finset Real

/-! ## 1. The additive characters of the cycle -/

theorem SpectralFreeWitness.chi_add_chi_neg(r k : ℕ) (m : ℤ) :
    chi r k m + chi r k (-m) = 2 * ((Real.cos (2 * π * ((k : ℝ) * (m : ℝ)) / r) : ℝ) : ℂ) := by sorry
