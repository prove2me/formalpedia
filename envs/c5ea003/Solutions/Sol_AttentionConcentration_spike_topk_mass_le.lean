-- Prove2me | solution 1 for AttentionConcentration.spike_topk_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:26:16.583531+00:00
-- url     : https://prove2.me/submissions/4e6eca31-58a5-4d95-923c-1189c6632ddf

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












open AttentionConcentration in
theorem solution(n k : ℕ) (T : Finset (Fin (n + 2))) (hk : T.card ≤ k) :
    ∑ i ∈ T, spike n i ≤ 1 / 2 + k / (2 * ((n : ℝ) + 1)) := by
  set c : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hpt : ∀ i : Fin (n + 2), spike n i ≤ (if i = 0 then (1:ℝ)/2 else 0) + c := by
    intro i
    by_cases h : i = 0
    · subst h
      have h0 : (if (0 : Fin (n + 2)) = 0 then (1:ℝ)/2 else 0) = 1/2 := by norm_num
      rw [spike_zero, h0]
      linarith
    · rw [spike_ne n h, ← hc]
      simp [h]
  have h1 : ∑ i ∈ T, spike n i ≤ ∑ i ∈ T, ((if i = 0 then (1:ℝ)/2 else 0) + c) :=
    Finset.sum_le_sum fun i _ => hpt i
  have h2 : ∑ i ∈ T, ((if i = 0 then (1:ℝ)/2 else 0) + c)
      = (∑ i ∈ T, (if i = 0 then (1:ℝ)/2 else 0)) + T.card * c := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h3 : ∑ i ∈ T, (if i = 0 then (1:ℝ)/2 else 0) ≤ 1 / 2 := by
    have hsub : ∑ i ∈ T, (if i = 0 then (1:ℝ)/2 else 0)
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin (n+2))), (if i = 0 then (1:ℝ)/2 else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) ?_
      intro i _ _
      split <;> norm_num
    simpa using hsub
  have h4 : (T.card : ℝ) * c ≤ (k : ℝ) * c :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hcpos.le
  have h5 : (k : ℝ) * c = k / (2 * ((n : ℝ) + 1)) := by rw [hc]; ring
  linarith [h1, h2.le, h2.ge, h3, h4, h5.le, h5.ge]
