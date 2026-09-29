-- Prove2me | Theorems.Thm_ProfileForm_one_div_exp_sub_one_gt
-- name    : ProfileForm.one_div_exp_sub_one_gt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:37:39.789464+00:00
-- url     : https://prove2.me/theorems/5f5cf7eb-4291-4645-a69a-df350ddb166e
-- title:
--   The exponential correction dominates near the origin: `1/x - 1/2 < 1/(e^x-1)`.
-- statement:
--   The exponential correction dominates near the origin: `1/x - 1/2 < 1/(e^x-1)`.
--
--   ```lean
--   theorem ProfileForm.one_div_exp_sub_one_gt{x : ℝ} (hx : 0 < x) :
--       1 / x - 1 / 2 < 1 / (Real.exp x - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormHumpThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormHumpThreshold.lean#L87

-- Thm stub generated from NumberTheory/ProfileFormHumpThreshold.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormHumpLocation
import Definitions.Def_NumberTheory_ProfileFormHumpThreshold
import Definitions.Def_NumberTheory_ProfileFormUniformMixturePeak

/-!
# Profile form IX: a critical exponent for the mixture hump

`ProfileFormUniformMixturePeak` proved that the residual of the power law
`T(x) = (1+x)^{-b}` against the uniform Dickman surrogate
`M(x) = (1 - e^{-x})/x` really does hump, for the measured exponent
`b = 11/10`, at `x ≈ 10`.  `ProfileFormHumpLocation` then explained the location
via the exact maximiser `x* = 1/(b-1)` of the elementary factor
`x (1+x)^{-b}`.

Both results leave open whether the hump is a *universal* feature of this
profile/baseline pair.  It is not.  The exact logarithmic derivative is

  `d/dx log (T/M)(x) = 1/x - b/(1+x) - 1/(e^x - 1)`,

so the hump is a competition between the algebraic term `1/x - b/(1+x)`, which
is positive up to `x* = 1/(b-1)`, and the exponential correction `1/(e^x - 1)`,
which is large exactly where `x` is small.  As `b` increases, `x*` shrinks into
the region where the correction dominates and the hump is destroyed.

Here we prove the destruction side rigorously:

* `exp_lt_pade` — the Padé bound `e^x < (2+x)/(2-x)` on `(0,2)`;
* `one_div_exp_sub_one_gt` — hence `1/x - 1/2 < 1/(e^x - 1)` for all `x > 0`;
* `uniformMixtureResidual_strictAntiOn` — **for every `b ≥ 3/2` the residual
  `T/M` is strictly decreasing on all of `(0,∞)`: no hump anywhere**;
* `uniform_hump_regime_bracket` — combined with the proved hump at `b = 11/10`,
  the humping regime is bracketed: it holds at `11/10` and fails from `3/2` on,
  so a critical exponent lies in `(11/10, 3/2)`.  Numerically it is
  `b_c ≈ 1.1605`, and the reported bootstrap interval `[0.991, 1.218]` straddles
  it — a second, independent way in which the experiment does not settle the
  qualitative shape.

The constant `3/2` is exactly what the two elementary bounds give: the argument
needs `1/(b-1) ≤ 2 ≤ 2b - 1`, i.e. `2b² - 3b ≥ 0`.
-/

open ProfileForm

open Set Filter Topology

theorem ProfileForm.one_div_exp_sub_one_gt{x : ℝ} (hx : 0 < x) :
    1 / x - 1 / 2 < 1 / (Real.exp x - 1) := by sorry
