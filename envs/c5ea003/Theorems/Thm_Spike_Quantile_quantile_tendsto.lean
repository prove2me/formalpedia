-- Prove2me | Theorems.Thm_Spike_Quantile_quantile_tendsto
-- name    : Spike.Quantile.quantile_tendsto
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:07:55.410029+00:00
-- url     : https://prove2.me/theorems/03c768ca-0cdd-4ec5-b217-9bf4a048f203
-- title:
--   The continuum limit law.
-- statement:
--   **The continuum limit law.**  For every level `y ∈ [0,8]` the empirical
--   fraction of window positions with residue at most `y M²` converges, as the
--   modulus grows, to `(√(1+y) - 1)/2`.
--
--   ```lean
--   theorem Spike.Quantile.quantile_tendsto(y : ℝ) (hy : 0 ≤ y) (hy8 : y ≤ 8) :
--       Tendsto (fun M : ℕ => empFrac M ⌊y * (M : ℝ) ^ 2⌋₊) atTop (nhds (limitCDF y)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SpikeQuantileLimitLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SpikeQuantileLimitLaw.lean#L136

-- Thm stub generated from Probability/SpikeQuantileLimitLaw.lean
import Mathlib
import Definitions.Def_Probability_SpikeInclusionGeometry
import Definitions.Def_Probability_SpikeQuantileIdentity
import Definitions.Def_Probability_SpikeQuantileLimitLaw

/-!
# The continuum quantile law of the window residue

`Catalog/Probability/SpikeQuantileIdentity.lean` proves the exact discrete
quantile identity

`#{ j ∈ W N : residue N j ≤ x } = min (3 isqrt N) (isqrt (N + x)) - isqrt N`.

This file closes the remaining, *asymptotic* half of future direction 1: the
limit law of the rescaled residue `v / s²` under the uniform position law on the
window.  Everything is proved with an explicit, non-asymptotic error term, so the
limit statement is a corollary rather than the primitive result.

Main results (`Spike.Quantile`):

* `card_sublevel_sq` : on a perfect-square modulus `N = M²` (where the integer
  and real square roots agree, so no rounding of the anchor occurs) the sublevel
  count is exactly `isqrt (M² + x) - M` as long as `x ≤ 8 M²`, i.e. as long as
  the threshold stays inside the window;
* `quantile_law_error` : the **Kolmogorov distance bound**
  `| F_M(x) - (√(1 + x/M²) - 1)/2 | ≤ 1/(2M)`
  where `F_M(x)` is the empirical fraction of window positions with residue at
  most `x`.  The limit c.d.f. `y ↦ (√(1+y) - 1)/2` is precisely the law of
  `(1 + 2U)² - 1` for `U` uniform on `[0,1]`, which is the conjectured law;
* `quantile_tendsto` : consequently, for every level `y ∈ [0,8]` the empirical
  fraction below `y M²` converges to `(√(1+y) - 1)/2`;
* `decile_law_exact` : at the round-85 decile level `y = 11/25` the limit law
  returns exactly `1/10`, and on the divisible moduli `N = (5m)²` the empirical
  fraction *equals* `1/10` with no error at all — the decile statistic and the
  magnitude statistic agree exactly, not just in the limit.

Interpretation: a first-decile analysis on this window is a `v ≤ 0.44 s²`
analysis with an error of at most one position, at every scale.  There is no
asymptotic regime in which the positional cut carries information beyond the
magnitude cut.
-/

open Spike.Quantile

open Spike Filter

/-! ### Comparison of the integer and real square roots -/




/-! ### The exact sublevel count on a perfect-square modulus -/




/-! ### The limit law, with an explicit error term -/

theorem Spike.Quantile.quantile_tendsto(y : ℝ) (hy : 0 ≤ y) (hy8 : y ≤ 8) :
    Tendsto (fun M : ℕ => empFrac M ⌊y * (M : ℝ) ^ 2⌋₊) atTop (nhds (limitCDF y)) := by sorry
