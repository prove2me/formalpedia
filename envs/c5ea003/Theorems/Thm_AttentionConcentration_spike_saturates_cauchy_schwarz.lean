-- Prove2me | Theorems.Thm_AttentionConcentration_spike_saturates_cauchy_schwarz
-- name    : AttentionConcentration.spike_saturates_cauchy_schwarz
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:57:31.403166+00:00
-- url     : https://prove2.me/theorems/8a7ddc3a-760d-4f5f-9731-71aeccb54d9d
-- title:
--   Sharpness of `sq_subset_mass_le` at `k = 1`.
-- statement:
--   **Sharpness of `sq_subset_mass_le` at `k = 1`.**  Along the spike family the
--   ratio of the squared top-1 mass to the Cauchy–Schwarz bound `1 · collision` tends
--   to `1`, so the constant in the truncation bound cannot be improved.
--
--   ```lean
--   theorem AttentionConcentration.spike_saturates_cauchy_schwarz:
--       Tendsto (fun n : ℕ => (spike n 0) ^ 2 / (1 * collision Finset.univ (spike n)))
--         atTop (𝓝 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AttentionConcentration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AttentionConcentration.lean#L296

-- Thm stub generated from Probability/AttentionConcentration.lean
import Mathlib
import Definitions.Def_Probability_AttentionConcentration
/-
# Concentration limits on top-`k` attention truncation

Empirical setting (round NET-36).  A trained causal transformer's attention rows
are probability vectors over `ctx` positions.  Two numbers are measured per model:

* the **effective support** `N_eff = 1 / ∑ p i ^ 2` (inverse participation ratio,
  a.k.a. inverse collision mass) of the attention rows, and
* the **knee** `k*`, the smallest `k` for which keeping only the `k` largest
  attention weights (and re-normalising) retains `≥ 0.98` of the full model's
  held-out accuracy.

This file proves the *information-theoretic side* of the story: what the measured
`N_eff` can and cannot say about top-`k` truncation.

Main results.

* `AttentionConcentration.sq_subset_mass_le` : for **every** index set `T`,
  `(∑_{i ∈ T} p i)^2 ≤ |T| · ∑_{i ∈ s} p i ^ 2`.  In particular the top-`k` mass is
  at most `sqrt (k / N_eff)` (`mass_le_sqrt_div_effSupport`).
* `AttentionConcentration.card_ge_of_retained` : retaining a fraction `ρ` of the
  attention *mass* forces `k ≥ ρ² · N_eff`.  This is a hard lower bound on the
  mass-knee, with no distributional assumption whatsoever.
* `AttentionConcentration.mass_knee_gt_measured_knee` : instantiated at the NET-36
  numbers (`N_eff = 152.11` at `ctx = 512`, measured `k* = 64`, `ρ = 0.98`) the
  bound gives `k_mass ≥ 146 > 64`.  Hence the measured accuracy-knee is *strictly*
  cheaper than any possible mass-knee: top-`k` attention truncation cannot be
  explained by mass retention — accuracy is genuinely more robust than attention
  mass.  This is a theorem-certified separation, not a fit.
* `AttentionConcentration.retained_mass_at_knee_le` : at the same numbers, a
  budget of `k ≤ 64` provably keeps at most `65 %` of the attention mass, while
  the measured retained accuracy there is `0.985`.
* `AttentionConcentration.effSupport_does_not_control_topk` : the converse of the
  Cauchy–Schwarz bound is false, and quantitatively so.  The spike-plus-uniform
  family has `N_eff → 4` while, for every fixed `k`, its top-`k` mass stays at
  `1/2`.  So a small effective support does *not* imply a small knee; the observed
  law `k* = d·ctx/32` must come from elsewhere (see `AttentionCostLaw.lean`).
* `AttentionConcentration.spike_saturates_cauchy_schwarz` : the same family shows
  the bound of `sq_subset_mass_le` is asymptotically sharp at `k = 1`.
-/


open AttentionConcentration

open Finset Filter Topology

variable {ι : Type*}








/-!
### Lab notes: the measured grid separates the mass knee from the accuracy knee

NET-36, cell B (`d = 4`, `ctx = 512`, seed 2): reported effective support
`N_eff = 152.11`, reported accuracy knee `k* = 64` at retention threshold `0.98`.
Cell A (`d = 16`, `ctx = 128`, seed 1): `N_eff = 52.73`, `k* = 64`.
-/




/-!
### The spike family: small effective support, stubborn top-`k` mass
-/

theorem AttentionConcentration.spike_saturates_cauchy_schwarz:
    Tendsto (fun n : ℕ => (spike n 0) ^ 2 / (1 * collision Finset.univ (spike n)))
      atTop (𝓝 1) := by sorry
