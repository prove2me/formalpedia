-- Prove2me | Theorems.Thm_ChebotarevGeodesic_HasLogErrorExponent_mono_log
-- name    : ChebotarevGeodesic.HasLogErrorExponent.mono_log
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:19:24.790334+00:00
-- url     : https://prove2.me/theorems/357f5c49-0e67-4c78-b2a9-743674156c91
-- title:
--   The staircase is upward closed in the log parameter.
-- statement:
--   The staircase is upward closed in the log parameter.
--
--   ```lean
--   theorem ChebotarevGeodesic.HasLogErrorExponent.mono_log(h : HasLogErrorExponent π M θ k) (hkj : k ≤ j) :
--       HasLogErrorExponent π M θ j := by sorry
--
--
--   /-! ## The staircase of a model error term
--
--   Throughout: `mdl M K θ k` is the counting function `M + K x^θ (log x)^k`. -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicStaircase.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicStaircase.lean#L46

-- Thm stub generated from Shared/ChebotarevGeodesicStaircase.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicStaircase
/-
# The two-parameter exponent staircase

Fifth research cycle on the paper *"Chebotarev geodesic theorem: non-split case"*.

`HasErrorExponent π M θ` (the shape "exponent `θ + ε`") deliberately forgets logarithmic
factors: `Shared.ChebotarevGeodesicTransfer` proves `optimalExponent (M + K x^θ log^k x) M = θ`
for every `k`.  The natural question left open there is what the `ε` actually hides.  This
file answers it completely for the model error terms produced by trace formulae.

We introduce the **two-parameter, `ε`-free** predicate

  `HasLogErrorExponent π M θ k  :  |π x − M x| ≤ C x^θ (log x)^k  for large x`,

show that its truth region is a *staircase* (upward closed in both parameters) whose
projection to the first coordinate recovers `HasErrorExponent`, and then compute the region
exactly for `π = M + K x^θ (log x)^k`:

  `HasLogErrorExponent π M θ' j ↔ θ < θ' ∨ (θ' = θ ∧ k ≤ j)`.

So the region has a single corner, at `(θ, k)`, and both coordinates of that corner are
genuine invariants of the pair `(π, M)`: the exponent `θ` *and* the log power `k`.  In
particular an error term `x^{25/36} (log x)^k` is not compatible with `x^{25/36} (log x)^{k−1}`,
which is precisely the information destroyed by writing "exponent `25/36 + ε`".
-/


open Finset Filter
open scoped Topology

open ChebotarevGeodesic


variable {π M : ℝ → ℝ} {θ θ' : ℝ} {k j : ℕ}

theorem ChebotarevGeodesic.HasLogErrorExponent.mono_log(h : HasLogErrorExponent π M θ k) (hkj : k ≤ j) :
    HasLogErrorExponent π M θ j := by sorry
