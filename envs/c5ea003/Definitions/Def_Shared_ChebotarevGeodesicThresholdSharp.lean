-- Prove2me | Definitions.Def_Shared_ChebotarevGeodesicThresholdSharp
-- name    : Shared_ChebotarevGeodesicThresholdSharp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:15.751485+00:00
-- url     : https://prove2.me/theorems/fd768569-776c-4f76-a88c-323349514a64
-- title:
--   Aether Catalog definitions — Shared_ChebotarevGeodesicThresholdSharp
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ChebotarevGeodesicThresholdSharp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ChebotarevGeodesicThresholdSharp.lean by skeleton subtraction
import Mathlib
/-
# Sharpness of the effective (Linnik-type) threshold

Continuation of `Shared.ChebotarevGeodesicEffective`, which proves

  `effective_lower_bound` : `π x ≥ (c/2)·x^β` for every `x ≥ max X₁ ((2C/c)^{2/(β-θ)})`

from the two hypotheses `|π - M| ≤ C x^{(θ+β)/2}` and `M x ≥ c x^β`.  Conjecture C3 of
`FUTURE_DIRECTIONS.md` asks whether the explicit threshold `(2C/c)^{2/(β-θ)}` is the true one.
It is: this file exhibits, for arbitrary admissible data `(c, C, θ, β)`, the extremal counting
function

  `criticalCount c C θ β x = c·x^β - C·x^{(θ+β)/2}`

for which the hypotheses hold with *equality*, and shows

* `criticalCount_error` : the error is exactly `C·x^{(θ+β)/2}`, so the data are admissible;
* `criticalCount_lt_half_of_lt_threshold` : *below* the threshold the conclusion **fails**
  everywhere, `π x < (c/2)·x^β`;
* `criticalCount_at_threshold` : *at* the threshold the conclusion holds with equality;
* `effective_threshold_sharp` : the packaged statement — the threshold of
  `effective_lower_bound` is attained and cannot be decreased;
* `effective_threshold_sharp_25_36` : the numerical instance of the paper, in which the
  least-geodesic threshold has the exact shape `(2C/c)^{72/11}`.
-/


open Filter
open scoped Topology

namespace ChebotarevGeodesic

/-- The extremal counting function for the effective threshold: main term `c x^β` minus the
largest admissible error `C x^{(θ+β)/2}`. -/
noncomputable def criticalCount (c C θ β x : ℝ) : ℝ := c * x ^ β - C * x ^ ((θ + β) / 2)







end ChebotarevGeodesic


