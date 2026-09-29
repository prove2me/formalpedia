-- Prove2me | Definitions.Def_Cryptography_FactoringBarriers_DFTSampleBound
-- name    : Cryptography_FactoringBarriers_DFTSampleBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:13:01.69945+00:00
-- url     : https://prove2.me/theorems/b39d1e46-5ff7-4d90-acc1-7c4febb45781
-- title:
--   Aether Catalog definitions — Cryptography_FactoringBarriers_DFTSampleBound
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.FactoringBarriers.DFTSampleBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/FactoringBarriers/DFTSampleBound.lean by skeleton subtraction
import Mathlib

/-!
# The Information-Theoretic DFT Sample Bound: `K ≥ r`

Shor's algorithm extracts the period `r` of `x ↦ a^x mod N` from the discrete
Fourier transform of a period-`r` signal.  A recurring hope for "classical
Shor" is that *few* Fourier samples might suffice.  This file proves that this
is impossible, in the strongest (representation-independent) form:

* `exists_indistinguishable_of_finrank_lt` — a linear measurement scheme with
  fewer measurements than the dimension of the signal space always confuses two
  distinct signals;
* `dft_lt_period_indistinguishable` — concretely: for `K < r` and *any* choice
  of `K` frequencies, two distinct period-`r` signals have identical DFT samples
  at those frequencies;
* `dft_sample_count_ge_period` — hence any family of sample frequencies that
  determines the signal must have `K ≥ r`.  This is the advertised bound.
* `dft_full_samples_determine` — sharpness: `r` samples (all frequencies) do
  determine the signal, since `ZMod.dft` is a linear equivalence.

The bound is unconditional and information-theoretic: it does not depend on the
computational model, only on `ℂ`-linearity of Fourier sampling.
-/

namespace FactoringBarriers

open Module

/-! ## The abstract dimension bound -/


/-! ## Fourier sampling on `ZMod r` -/

variable {r K : ℕ} [NeZero r]

/-- The measurement map "take the DFT, then read off the `K` chosen
frequencies", as a `ℂ`-linear map. -/
noncomputable def dftSample (idx : Fin K → ZMod r) :
    (ZMod r → ℂ) →ₗ[ℂ] (Fin K → ℂ) :=
  (LinearMap.funLeft ℂ ℂ idx).comp (ZMod.dft : (ZMod r → ℂ) ≃ₗ[ℂ] (ZMod r → ℂ)).toLinearMap








end FactoringBarriers


