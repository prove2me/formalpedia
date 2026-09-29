-- Prove2me | Definitions.Def_Shared_ChebotarevGeodesicStaircase
-- name    : Shared_ChebotarevGeodesicStaircase
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:15.536037+00:00
-- url     : https://prove2.me/theorems/c5ac8bc7-93aa-4a56-8e73-8a9c5669dfe1
-- title:
--   Aether Catalog definitions — Shared_ChebotarevGeodesicStaircase
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ChebotarevGeodesicStaircase`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ChebotarevGeodesicStaircase.lean by skeleton subtraction
import Mathlib
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

namespace ChebotarevGeodesic

/-- The `ε`-free two-parameter error predicate: `|π − M| ≤ C x^θ (log x)^k` for large `x`.
This is literally the shape a trace-formula computation outputs. -/
def HasLogErrorExponent (π M : ℝ → ℝ) (θ : ℝ) (k : ℕ) : Prop :=
  ∃ C > 0, ∃ X ≥ (1 : ℝ), ∀ x ≥ X, |π x - M x| ≤ C * x ^ θ * (Real.log x) ^ k

variable {π M : ℝ → ℝ} {θ θ' : ℝ} {k j : ℕ}





/-! ## The staircase of a model error term

Throughout: `mdl M K θ k` is the counting function `M + K x^θ (log x)^k`. -/

/-- The model counting function `M(x) + K x^θ (log x)^k`. -/
noncomputable def mdl (M : ℝ → ℝ) (K θ : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun x => M x + K * x ^ θ * (Real.log x) ^ k








end ChebotarevGeodesic


