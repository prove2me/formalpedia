-- Prove2me | solution 1 for F1Tightness.scanCost_le_polCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:11:51.769441+00:00
-- url     : https://prove2.me/submissions/799d7ffc-328f-4c4a-a8db-a902703d3c9e

-- Sol generated from Probability/F1TightnessCore.lean
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











/-! ## The identity chain -/






/-! ## The mean-position form of the identity chain -/




/-! ## Monotonicity of the gap factor in `Λ` -/




/-! ## Rearrangement: the ascending policy is optimal on a front-loaded profile -/



/-! ## Strict slack: an antitone non-flat profile cannot attain the bound -/








/-! ## The tightness-circularity catch: `q̂` is not identified -/




/-! ## The measured profile: numerical corollaries -/









open F1Tightness in
theorem solution{p : Fin M → ℝ} (hanti : Antitone p)
    (σ : Equiv.Perm (Fin M)) : scanCost p ≤ polCost p σ := by
  have hav : Antivary p (fun i : Fin M => (((i : ℕ) : ℝ) + 1)) := by
    intro i j hij
    have hlt : i < j := by
      by_contra hji
      push_neg at hji
      have : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by
        exact_mod_cast Fin.le_iff_val_le_val.mp hji
      simp only at hij
      linarith
    exact hanti hlt.le
  have hre := hav.sum_smul_le_sum_smul_comp_perm (σ := σ)
  simp only [smul_eq_mul] at hre
  unfold scanCost polCost
  calc ∑ i : Fin M, (((i : ℕ) : ℝ) + 1) * p i
      = ∑ i : Fin M, p i * (((i : ℕ) : ℝ) + 1) := Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i : Fin M, p i * (((σ i : ℕ) : ℝ) + 1) := hre
    _ = ∑ i : Fin M, (((σ i : ℕ) : ℝ) + 1) * p i :=
        Finset.sum_congr rfl fun i _ => by ring
