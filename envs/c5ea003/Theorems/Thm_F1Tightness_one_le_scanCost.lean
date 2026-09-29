-- Prove2me | Theorems.Thm_F1Tightness_one_le_scanCost
-- name    : F1Tightness.one_le_scanCost
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:21:59.687664+00:00
-- url     : https://prove2.me/theorems/19cb2ad8-891f-486f-a3db-0228ef8cc350
-- title:
--   One le scanCost
-- statement:
--   Formal statement of `F1Tightness.one_le_scanCost` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem F1Tightness.one_le_scanCost{p : Fin M → ℝ} (hp : ∀ i, 0 ≤ p i)
--       (hsum : ∑ i : Fin M, p i = 1) : 1 ≤ scanCost p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessCore.lean#L156

-- Thm stub generated from Probability/F1TightnessCore.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore

/-!
# F1 tightness: the slack factor of the master speed-up inequality (paper 250)

This file formalises the *shape layer* of the round-92 "F1-TIGHTNESS-CONNECTION"
deliverable.  The empirical situation is the following.  A scan visits the `M`
cells of a window one after another; the target sits in cell `i` with prior
probability `p i` (the measured **positional profile**, front-loaded, harmonic).
A *policy* is a permutation `σ` of the cells: it probes cell `i` at rank
`σ i + 1`, so its expected probe count is `polCost p σ = ∑ i, (σ i + 1) * p i`.

Three costs organise everything:

* `scanCost p` — the cost of the **ascending** (identity) policy;
* `revCost p`  — the cost of the **descending** (reversed) policy;
* `baseCost M = (M+1)/2` — the cost under a flat profile / random order.

The F1 master inequality of paper 225 reads `S ≤ 1/(Λ·Θ·q̂)`.  On this pool the
parameters are the *cost ratios*

  `Lam p = scanCost / revCost`,   `Theta p = scanCost / baseCost`,   `q̂ = 1`,

and the realizable ascending speed-up is `Sasc p = revCost / scanCost = 1/Λ`.

Main results.

* `scanCost_add_revCost_eq` — the **conservation identity** `c_asc + c_desc = M+1
  = 2·C₀`.  Everything below follows from this single identity: the whole
  parameter map is a one-parameter family.
* `gapX_eq_gapOfLam`, `Theta_eq_of_Lam` — `X = (1+Λ)/(2Λ)` and `Θ = 2Λ/(1+Λ)`
  exactly (no continuum approximation), so `X = 1/Θ`.
* `slack_identity` — `bound = X · S_asc`: the gap between the proven bound and
  the realizable ascending speed-up is exactly the factor `X`, *policy- and
  baseline-independent*.
* `policy_speedup_le_Sasc` — rearrangement: on an antitone (front-loaded)
  profile no policy beats the ascending scan, so `S_asc` is the best realizable
  speed-up.
* `scanCost_lt_baseCost` / `one_lt_gapX` — **strict slack from non-flatness**:
  an antitone profile that is not flat has `X > 1` strictly (a strict Chebyshev
  inequality, proved here from a pairwise identity).
* `no_policy_attains_bound`, `speedup_lt_bound` — consequently *no* realizable
  policy attains the master bound; every policy's speed-up is at most
  `bound / X < bound`.
* `gapX_eq_one_iff`, `gapX_flat` — equality `X = 1` happens exactly when the
  ascending cost equals the flat baseline, in particular for the flat profile;
  this is the equality case that the three independent tests (KS, LRT,
  conditional-logistic LRT) refute on the measured pool.
* `qhat_nonidentifiable`, `anchor_inversion_tautology` — the
  **tightness-circularity catch**: with `q̂` free, *any* observed speed-up can be
  turned into an exact equality, so an anchor whose parameters were obtained by
  inverting the law carries zero evidential weight for attainment.
* Numerical corollaries (`measured_gapX_approx`, `gapX_mem_interval`,
  `measured_bound_approx`, `predicted_speedup_lt_bound`) reproduce the booked
  numbers `Λ = 0.765671`, `Θ ≈ 0.867`, `X ≈ 1.15302 ∈ [1.10, 1.23]`,
  `S ≈ 1.306`, `bound ≈ 1.506`.
-/

open Finset

open F1Tightness

/-! ## A pairwise identity and a strict Chebyshev inequality -/

variable {ι : Type*}



/-! ## Costs of a scan policy -/

variable {M : ℕ}












/-! ## The conservation identity and positivity -/

theorem F1Tightness.one_le_scanCost{p : Fin M → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i : Fin M, p i = 1) : 1 ≤ scanCost p := by sorry
