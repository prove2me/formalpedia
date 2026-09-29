-- Prove2me | Theorems.Thm_FactoringBarriers_dft_sample_count_ge_period
-- name    : FactoringBarriers.dft_sample_count_ge_period
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:50:11.701232+00:00
-- url     : https://prove2.me/theorems/0a53967e-a771-4e1a-ac33-50e0f8dd95b3
-- title:
--   The sample lower bound `K ≥ r`.
-- statement:
--   **The sample lower bound `K ≥ r`.** If a family of `K` sample frequencies
--   suffices to determine every period-`r` signal from its Fourier samples, then
--   `K ≥ r`.
--
--   ```lean
--   theorem FactoringBarriers.dft_sample_count_ge_period(idx : Fin K → ZMod r)
--       (hdet : ∀ v w : ZMod r → ℂ, (∀ j : Fin K, ZMod.dft v (idx j) = ZMod.dft w (idx j)) → v = w) :
--       r ≤ K := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FactoringBarriers/DFTSampleBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FactoringBarriers/DFTSampleBound.lean#L74

-- Thm stub generated from Cryptography/FactoringBarriers/DFTSampleBound.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_DFTSampleBound

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

open FactoringBarriers

open Module

/-! ## The abstract dimension bound -/


/-! ## Fourier sampling on `ZMod r` -/

variable {r K : ℕ} [NeZero r]

theorem FactoringBarriers.dft_sample_count_ge_period(idx : Fin K → ZMod r)
    (hdet : ∀ v w : ZMod r → ℂ, (∀ j : Fin K, ZMod.dft v (idx j) = ZMod.dft w (idx j)) → v = w) :
    r ≤ K := by sorry
