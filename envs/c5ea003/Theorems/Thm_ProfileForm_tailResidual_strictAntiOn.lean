-- Prove2me | Theorems.Thm_ProfileForm_tailResidual_strictAntiOn
-- name    : ProfileForm.tailResidual_strictAntiOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:37:51.576902+00:00
-- url     : https://prove2.me/theorems/c419c959-6984-4f37-9404-7d091dc30850
-- title:
--   TailResidual strictAntiOn
-- statement:
--   Formal statement of `ProfileForm.tailResidual_strictAntiOn` from the Aether Catalog (NumberTheory). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ProfileForm.tailResidual_strictAntiOn{b : ℝ} (hb : 1 < b) :
--       StrictAntiOn (tailResidual b) (Ici (humpLocation b)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormHumpLocation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormHumpLocation.lean#L121

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

theorem ProfileForm.tailResidual_strictAntiOn{b : ℝ} (hb : 1 < b) :
    StrictAntiOn (tailResidual b) (Ici (humpLocation b)) := by sorry
