-- Prove2me | Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
-- name    : MachineLearning_NoiseFloor_EffectiveDimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:55.020346+00:00
-- url     : https://prove2.me/theorems/4ba29a11-79b6-4521-bae7-7a73a957573a
-- title:
--   Aether Catalog definitions — MachineLearning_NoiseFloor_EffectiveDimension
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.NoiseFloor.EffectiveDimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/NoiseFloor/EffectiveDimension.lean by skeleton subtraction
import Mathlib
/-
# The Noise-Floor Principle, Part I: Effective Dimension

Round-6 hypothesis closure, Phase A.  This file develops the *spectral effective
dimension*

  `effDim a b = ∑ i, a i / (a i + b)`

of a nonnegative "signal spectrum" `a : ι → ℝ` measured at a "noise level" `b > 0`.
It is the scalar shadow of the matrix quantity `tr (A (A + b•1)⁻¹)` (the
*trace lemma frontier*, formalised in `TraceLemma.lean`), and it is the exact
value of the information-theoretic noise floor of any linear spectral filter
(formalised in `NoiseFloorPrinciple.lean`).

Main results:

* `effDim_nonneg`, `effDim_le_card`, `effDim_le_min`
* `effDim_le_trace_div`      — the *trace bound* `d_eff ≤ tr(a)/b`
* `effDim_antitone_level`    — monotone decreasing in the noise level
* `effDim_mono_spectrum`     — monotone increasing in the spectrum
* `effDim_doubling`          — `d_eff(b/2) ≤ 2 d_eff(b)`: the noise floor has no
                               sharp cliff (a Muckenhoupt-style doubling property)
* `effDim_scale_invariant`   — joint scaling invariance `d_eff(ca, cb) = d_eff(a,b)`
* `effDim_concave`           — concavity in the spectrum (mixing signals cannot help)
* `count_le_two_mul_effDim`  — `#{i : b ≤ a i} ≤ 2 d_eff`: every *resolvable* mode
                               contributes at least one half to the effective dimension.
-/

namespace Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]

/-- The **spectral effective dimension** of a nonnegative spectrum `a` at noise
level `b`: `∑ i, a i / (a i + b)`.  Each mode contributes a number in `[0,1)`
measuring how far it sticks out of the noise floor. -/
noncomputable def effDim (a : ι → ℝ) (b : ℝ) : ℝ := ∑ i, a i / (a i + b)

section Basic

variable {a : ι → ℝ} {b : ℝ}












end Basic

section Counting

variable {a : ι → ℝ} {b : ℝ}



end Counting

end Catalog.MachineLearning.NoiseFloor


