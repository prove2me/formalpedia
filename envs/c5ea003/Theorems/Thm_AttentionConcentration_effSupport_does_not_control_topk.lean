-- Prove2me | Theorems.Thm_AttentionConcentration_effSupport_does_not_control_topk
-- name    : AttentionConcentration.effSupport_does_not_control_topk
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:57:06.630848+00:00
-- url     : https://prove2.me/theorems/622ec482-e840-415d-810e-5e44b21a34cf
-- title:
--   The effective support does not control the knee.
-- statement:
--   **The effective support does not control the knee.**  For every fixed budget
--   `k` and every tolerance `ε > 0` there is an attention row whose effective support
--   is within `ε` of `4` — i.e. "essentially four positions matter" — yet whose best
--   `k`-position truncation retains barely more than half of the mass.  Consequently no
--   inequality of the form "top-`k` mass `≥ F(k, N_eff)`" with `F(k,4) > 1/2` can hold,
--   and the empirical law `k* = d·ctx/32` cannot be a consequence of concentration
--   alone: the measured effective supports are *not* sufficient statistics for the
--   knee.
--
--   ```lean
--   theorem AttentionConcentration.effSupport_does_not_control_topk(k : ℕ) {ε : ℝ} (hε : 0 < ε) :
--       ∃ (n : ℕ), |effSupport Finset.univ (spike n) - 4| < ε ∧
--         ∀ T : Finset (Fin (n + 2)), T.card ≤ k → ∑ i ∈ T, spike n i < 1 / 2 + ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AttentionConcentration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AttentionConcentration.lean#L263

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

theorem AttentionConcentration.effSupport_does_not_control_topk(k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ), |effSupport Finset.univ (spike n) - 4| < ε ∧
      ∀ T : Finset (Fin (n + 2)), T.card ≤ k → ∑ i ∈ T, spike n i < 1 / 2 + ε := by sorry
