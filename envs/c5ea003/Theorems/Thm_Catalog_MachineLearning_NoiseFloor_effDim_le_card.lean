-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_effDim_le_card
-- name    : Catalog.MachineLearning.NoiseFloor.effDim_le_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:27:29.799931+00:00
-- url     : https://prove2.me/theorems/5f1be4f9-4923-4c10-80ed-de898727c52d
-- title:
--   The effective dimension never exceeds the ambient dimension.
-- statement:
--   The effective dimension never exceeds the ambient dimension.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.effDim_le_card(ha : ∀ i, 0 ≤ a i) (hb : 0 < b) :
--       effDim a b ≤ (Fintype.card ι : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/EffectiveDimension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/EffectiveDimension.lean#L58

-- Thm stub generated from MachineLearning/NoiseFloor/EffectiveDimension.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
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

open Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]



variable {a : ι → ℝ} {b : ℝ}

theorem Catalog.MachineLearning.NoiseFloor.effDim_le_card(ha : ∀ i, 0 ≤ a i) (hb : 0 < b) :
    effDim a b ≤ (Fintype.card ι : ℝ) := by sorry
