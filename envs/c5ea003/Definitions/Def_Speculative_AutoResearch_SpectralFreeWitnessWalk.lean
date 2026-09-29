-- Prove2me | Definitions.Def_Speculative_AutoResearch_SpectralFreeWitnessWalk
-- name    : Speculative_AutoResearch_SpectralFreeWitnessWalk
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:31:25.963718+00:00
-- url     : https://prove2.me/theorems/e23d80ce-edd8-4358-ad15-857990a08193
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_SpectralFreeWitnessWalk
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.SpectralFreeWitnessWalk`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/SpectralFreeWitnessWalk.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
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


namespace SpectralFreeWitness

open Finset Real

/-! ## 1. The additive characters of the cycle -/

/-- The additive character `χ_k (x) = exp (2π i k x / r)` of `Z/rZ`, realised as a
function on `ℤ` (it is `r`-periodic). -/
noncomputable def chi (r k : ℕ) (x : ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ((k : ℂ) * (x : ℂ)) / r)




/-! ## 2. The diffusion operator -/

/-- One step of the half-lazy random walk with lacunary dyadic generators
`{± 2^t : t ≤ M}` on the cycle `Z/rZ`. -/
noncomputable def walkStep (M : ℕ) (f : ℤ → ℂ) : ℤ → ℂ := fun x =>
  f x / 2 + (∑ t ∈ range (M + 1), (f (x + 2 ^ t) + f (x - 2 ^ t))) / (4 * ((M : ℂ) + 1))







/-! ## 3. Fourier expansion of the delta function -/

/-- The periodic delta function at the identity of `Z/rZ`. -/
noncomputable def deltaPer (r : ℕ) : ℤ → ℂ := fun x => if (r : ℤ) ∣ x then 1 else 0


/-! ## 4. The return probability equals the spectral heat kernel -/



end SpectralFreeWitness


