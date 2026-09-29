-- Prove2me | solution 1 for AttentionConcentration.spike_effSupport_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:26:15.871809+00:00
-- url     : https://prove2.me/submissions/7fc39d8f-e764-47b1-8dce-feaac2d34aec

-- Sol generated from Probability/AttentionConcentration.lean
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


@[simp] lemma spike_zero (n : ℕ) : spike n 0 = 1 / 2 := by
  unfold spike; norm_num

lemma spike_ne (n : ℕ) {i : Fin (n + 2)} (h : i ≠ 0) :
    spike n i = 1 / (2 * ((n : ℝ) + 1)) := by
  unfold spike; simp [h]



lemma spike_collision (n : ℕ) :
    collision Finset.univ (spike n) = ((n : ℝ) + 2) / (4 * ((n : ℝ) + 1)) := by
  have h : ∀ i : Fin (n + 1), spike n i.succ ^ 2 = (1 / (2 * ((n : ℝ) + 1))) ^ 2 :=
    fun i => by rw [spike_ne n (Fin.succ_ne_zero i)]
  unfold collision
  rw [Fin.sum_univ_succ, spike_zero, Finset.sum_congr rfl (fun i _ => h i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring


lemma spike_effSupport (n : ℕ) :
    effSupport Finset.univ (spike n) = 4 * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
  unfold effSupport
  rw [spike_collision]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp


private lemma tendsto_one_div_succ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat





open AttentionConcentration in
theorem solution:
    Tendsto (fun n : ℕ => effSupport Finset.univ (spike n)) atTop (𝓝 4) := by
  have h : ∀ n : ℕ, effSupport Finset.univ (spike n) = 4 * (1 + 1 / ((n : ℝ) + 1))⁻¹ := by
    intro n
    rw [spike_effSupport]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    rw [eq_comm, mul_inv_eq_iff_eq_mul₀ (by positivity)]
    field_simp
    ring
  simp only [h]
  have hden : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_succ
  have := (hden.inv₀ (by norm_num)).const_mul (4 : ℝ)
  simpa using this
