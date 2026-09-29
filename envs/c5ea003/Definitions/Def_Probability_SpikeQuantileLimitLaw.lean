-- Prove2me | Definitions.Def_Probability_SpikeQuantileLimitLaw
-- name    : Probability_SpikeQuantileLimitLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:13.360076+00:00
-- url     : https://prove2.me/theorems/e5147b77-875e-45e1-82c8-f4d0f3aa6eb8
-- title:
--   Aether Catalog definitions — Probability_SpikeQuantileLimitLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SpikeQuantileLimitLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SpikeQuantileLimitLaw.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_SpikeInclusionGeometry
import Definitions.Def_Probability_SpikeQuantileIdentity

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

namespace Spike.Quantile

open Spike Filter

/-! ### Comparison of the integer and real square roots -/




/-! ### The exact sublevel count on a perfect-square modulus -/




/-! ### The limit law, with an explicit error term -/

/-- The empirical fraction of window positions of the modulus `M²` whose residue
is at most `x`. -/
noncomputable def empFrac (M x : ℕ) : ℝ :=
  (((window (M ^ 2)).filter (fun j => residue (M ^ 2) j ≤ x)).card : ℝ) / (2 * M)

/-- The conjectured limit c.d.f.: the law of `(1 + 2U)² - 1` for `U` uniform on
`[0,1]`, i.e. `y ↦ (√(1+y) - 1)/2`. -/
noncomputable def limitCDF (y : ℝ) : ℝ := (Real.sqrt (1 + y) - 1) / 2




/-! ### The decile point: the limit law is attained exactly -/



end Spike.Quantile


