-- Prove2me | Theorems.Thm_ProfileForm_tailResidual_tendsto_zero
-- name    : ProfileForm.tailResidual_tendsto_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:38:03.772635+00:00
-- url     : https://prove2.me/theorems/e25b8d68-3391-4e16-ab69-e6517e1db6b3
-- title:
--   The confinement hypothesis is not vacuous: it holds for all large `x`,
-- statement:
--   The confinement hypothesis is not vacuous: it holds for all large `x`,
--   because for `b > 1` the tail residual tends to `0` at infinity.
--
--   ```lean
--   theorem ProfileForm.tailResidual_tendsto_zero{b : ℝ} (hb : 1 < b) :
--       Tendsto (tailResidual b) atTop (𝓝 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormHumpLocation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormHumpLocation.lean#L236

-- Thm stub generated from NumberTheory/ProfileFormHumpLocation.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormHumpLocation
import Definitions.Def_NumberTheory_ProfileFormResidualPeak

/-!
# Profile form VIII: the hump-location law

Stage-5 result of the cycle: we close the main open conjecture left by
`ProfileFormUniformMixturePeak` (Direction 1 of `FUTURE_DIRECTIONS.md`).

`ProfileFormUniformMixturePeak` exhibited a hump of the uniform-mixture residual
`R(x) = T(x)/M(x)` near `x ≈ 10` for the measured exponent `b = 11/10`, and
observed numerically that the hump sits near `1/(b-1) ≈ 9.6`.  Here that
observation becomes a theorem.

Write `T(x) = (1+x)^{-b}` and `M(x) = (1 - e^{-x})/x`.  Then exactly

  `R(x) = tailResidual b x / (1 - e^{-x})`,   `tailResidual b x = x (1+x)^{-b}`,

and the second factor tends to `1`, so the *shape* of `R` far from the origin is
governed by the elementary function `tailResidual`.  Its logarithmic derivative

  `d/dx log (x (1+x)^{-b}) = 1/x - b/(1+x) = (1 - (b-1)x) / (x(1+x))`

changes sign exactly once, at

  `x* = 1/(b-1)`,

for every `b > 1`.  This gives:

* `tailResidual_strictMonoOn` / `tailResidual_strictAntiOn` — strict increase on
  `[0, x*]`, strict decrease on `[x*, ∞)`;
* `tailResidual_unique_max` — `x*` is the *unique* maximiser on `[0,∞)`;
* `humpLocation_eleven_tenths` — the closed form `x* = 1/(b-1)` is exactly `10`
  at the measured exponent `b = 11/10`, matching the numerically located hump;
* `uniformResidual_hump_confined` — a quantitative transfer to the true
  residual: outside the set where `tailResidual` is within a factor
  `1 - e^{-x₀}` of its maximum, the true residual is strictly below its value at
  `x*`.  So the hump of `R` really is confined near `1/(b-1)`.

The law is a genuine *dichotomy* with the `b = 1` threshold of
`ProfileFormExponentThreshold`: for `b ≤ 1` no such maximiser exists,
`tailResidual` being then increasing throughout (`tailResidual_strictMono_of_le_one`).
So the same exponent-one threshold that decides the total window mass also
decides whether a hump exists at all — and the reported bootstrap interval
`[0.991, 1.218]` straddles it.
-/

open ProfileForm

open Set Filter Topology
















/-! ### Transfer to the true uniform-mixture residual -/

theorem ProfileForm.tailResidual_tendsto_zero{b : ℝ} (hb : 1 < b) :
    Tendsto (tailResidual b) atTop (𝓝 0) := by sorry
