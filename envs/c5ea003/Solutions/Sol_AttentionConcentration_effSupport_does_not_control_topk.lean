-- Prove2me | solution 1 for AttentionConcentration.effSupport_does_not_control_topk
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:53:06.774636+00:00
-- url     : https://prove2.me/submissions/090fd590-1378-4578-abb1-cdd44900b472

-- Sol generated from Probability/AttentionConcentration.lean
import Mathlib
import Definitions.Def_Probability_AttentionConcentration
import Theorems.Thm_AttentionConcentration_spike_effSupport_tendsto
import Theorems.Thm_AttentionConcentration_spike_topk_mass_le
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










private lemma tendsto_one_div_succ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat





open AttentionConcentration in
theorem solution(k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ), |effSupport Finset.univ (spike n) - 4| < ε ∧
      ∀ T : Finset (Fin (n + 2)), T.card ≤ k → ∑ i ∈ T, spike n i < 1 / 2 + ε := by
  have hA : ∀ᶠ n : ℕ in atTop, |effSupport Finset.univ (spike n) - 4| < ε := by
    have h := spike_effSupport_tendsto
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa [Real.dist_eq] using hN n hn
  have hB : ∀ᶠ n : ℕ in atTop, (k : ℝ) / (2 * ((n : ℝ) + 1)) < ε := by
    have hlim : Tendsto (fun n : ℕ => (k : ℝ) / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h2 := tendsto_one_div_succ.const_mul ((k : ℝ) / 2)
      rw [mul_zero] at h2
      exact h2.congr (fun n => by rw [div_mul_div_comm, mul_one])
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨N, hN⟩ := hlim ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  obtain ⟨n, hn1, hn2⟩ := (hA.and hB).exists
  refine ⟨n, hn1, fun T hT => ?_⟩
  have := spike_topk_mass_le n k T hT
  linarith
