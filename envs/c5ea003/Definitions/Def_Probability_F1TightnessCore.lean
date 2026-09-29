-- Prove2me | Definitions.Def_Probability_F1TightnessCore
-- name    : Probability_F1TightnessCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:10.56706+00:00
-- url     : https://prove2.me/theorems/4c4b63c9-9659-4e2c-aa95-c0499521688b
-- title:
--   Aether Catalog definitions — Probability_F1TightnessCore
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.F1TightnessCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/F1TightnessCore.lean by skeleton subtraction
import Mathlib

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

namespace F1Tightness

/-! ## A pairwise identity and a strict Chebyshev inequality -/

variable {ι : Type*}



/-! ## Costs of a scan policy -/

variable {M : ℕ}

/-- Expected probe count of the **ascending** (identity) policy: cell `i` is
probed at rank `i+1`. -/
noncomputable def scanCost (p : Fin M → ℝ) : ℝ := ∑ i : Fin M, (((i : ℕ) : ℝ) + 1) * p i

/-- Expected probe count of the **descending** (reversed) policy: cell `i` is
probed at rank `M - i`. -/
noncomputable def revCost (p : Fin M → ℝ) : ℝ := ∑ i : Fin M, ((M : ℝ) - ((i : ℕ) : ℝ)) * p i

/-- Baseline cost `C₀ = (M+1)/2`: the expected probe count of any policy under a
flat profile (equivalently, of a random order under any profile). -/
noncomputable def baseCost (M : ℕ) : ℝ := ((M : ℝ) + 1) / 2

/-- Expected probe count of the policy `σ`, which probes cell `i` at rank
`σ i + 1`. -/
noncomputable def polCost (p : Fin M → ℝ) (σ : Equiv.Perm (Fin M)) : ℝ :=
  ∑ i : Fin M, (((σ i : ℕ) : ℝ) + 1) * p i

/-- The F1 shape parameter `Λ`: ratio of the ascending to the descending cost.
`1/Λ` is the ascending-over-descending gain. -/
noncomputable def Lam (p : Fin M → ℝ) : ℝ := scanCost p / revCost p

/-- The F1 alignment parameter `Θ`: the ascending cost normalised by the flat
baseline. -/
noncomputable def Theta (p : Fin M → ℝ) : ℝ := scanCost p / baseCost M

/-- The gap (slack) factor `X = C₀ / c_asc`. -/
noncomputable def gapX (p : Fin M → ℝ) : ℝ := baseCost M / scanCost p

/-- Realizable speed-up of the policy `σ`, measured against the anti-aligned
(descending) policy. -/
noncomputable def speedup (p : Fin M → ℝ) (σ : Equiv.Perm (Fin M)) : ℝ :=
  revCost p / polCost p σ

/-- The realizable ascending speed-up `S_asc = 1/Λ`. -/
noncomputable def Sasc (p : Fin M → ℝ) : ℝ := revCost p / scanCost p

/-- The right-hand side of the paper-225 master inequality,
`bound = 1/(Λ·Θ·q̂)` (arm 1, `k_bits = 0`). -/
noncomputable def boundF1 (lam th q : ℝ) : ℝ := 1 / (lam * th * q)

/-- `X` as a function of `Λ` alone. -/
noncomputable def gapOfLam (lam : ℝ) : ℝ := (1 + lam) / (2 * lam)

/-! ## The conservation identity and positivity -/











/-! ## The identity chain -/






/-! ## The mean-position form of the identity chain -/

/-- Mean normalised probe position `E_x = ∑ ((i + 1/2)/M) · p i`, the coordinate
in which the measured profile is reported. -/
noncomputable def meanPos (p : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, ((((i : ℕ) : ℝ) + 1 / 2) / (M : ℝ)) * p i



/-! ## Monotonicity of the gap factor in `Λ` -/




/-! ## Rearrangement: the ascending policy is optimal on a front-loaded profile -/



/-! ## Strict slack: an antitone non-flat profile cannot attain the bound -/








/-! ## The tightness-circularity catch: `q̂` is not identified -/




/-! ## The measured profile: numerical corollaries -/

/-- The measured shape parameter `Λ = 0.765671`. -/
noncomputable def LamMeas : ℝ := 765671 / 1000000







end F1Tightness


