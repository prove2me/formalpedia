-- Prove2me | Theorems.Thm_SpectralFreeWitness_sum_chi
-- name    : SpectralFreeWitness.sum_chi
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:52:22.300178+00:00
-- url     : https://prove2.me/theorems/7e87b10f-2ed7-4a4e-a44f-fbd2795911e1
-- title:
--   Character orthogonality on `Z/rZ`.
-- statement:
--   **Character orthogonality** on `Z/rZ`.
--
--   ```lean
--   theorem SpectralFreeWitness.sum_chi(r : ℕ) (hr : 0 < r) (x : ℤ) :
--       ∑ k ∈ range r, chi r k x = r * deltaPer r x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/SpectralFreeWitnessWalk.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/SpectralFreeWitnessWalk.lean#L157

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





/-! ## 2. The diffusion operator -/








/-! ## 3. Fourier expansion of the delta function -/

theorem SpectralFreeWitness.sum_chi(r : ℕ) (hr : 0 < r) (x : ℤ) :
    ∑ k ∈ range r, chi r k x = r * deltaPer r x := by sorry
