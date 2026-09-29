-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_mode_concave
-- name    : Catalog.MachineLearning.NoiseFloor.mode_concave
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:27:21.501538+00:00
-- url     : https://prove2.me/theorems/50148ea7-3b2d-4e1e-ba7b-9f2b870dc4e3
-- title:
--   Pointwise concavity of `x ↦ x / (x + b)` on the nonnegative reals.
-- statement:
--   Pointwise concavity of `x ↦ x / (x + b)` on the nonnegative reals.  The
--   cleared-denominator identity behind it is
--   `gap = b * w * (1-w) * (x-y)^2`.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.mode_concave{x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 < b) {w : ℝ}
--       (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
--       w * (x / (x + b)) + (1 - w) * (y / (y + b))
--         ≤ (w * x + (1 - w) * y) / ((w * x + (1 - w) * y) + b) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/EffectiveDimension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/EffectiveDimension.lean#L118

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

theorem Catalog.MachineLearning.NoiseFloor.mode_concave{x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 < b) {w : ℝ}
    (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
    w * (x / (x + b)) + (1 - w) * (y / (y + b))
      ≤ (w * x + (1 - w) * y) / ((w * x + (1 - w) * y) + b) := by sorry
