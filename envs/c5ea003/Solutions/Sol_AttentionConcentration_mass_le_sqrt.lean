-- Prove2me | solution 1 for AttentionConcentration.mass_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:31:35.270976+00:00
-- url     : https://prove2.me/submissions/f101275b-6f37-43ea-b0b0-91e60c0c5e1c

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




/-- **Cauchy–Schwarz truncation bound.**  For any set `T` of retained positions
inside the support `s`, the retained mass squared is at most `|T|` times the
collision mass.  No sign or normalisation assumption is needed, and `T` need not
be the set of `|T|` largest weights — so this bounds the top-`k` mass as well. -/
theorem sq_subset_mass_le (s T : Finset ι) (p : ι → ℝ) (hT : T ⊆ s) :
    (∑ i ∈ T, p i) ^ 2 ≤ T.card * collision s p := by
  have h1 : (∑ i ∈ T, p i) ^ 2 ≤ T.card * ∑ i ∈ T, p i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : ∑ i ∈ T, p i ^ 2 ≤ collision s p :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun i _ _ => sq_nonneg _)
  refine h1.trans ?_
  have : (0:ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left h2 this




/-!
### Lab notes: the measured grid separates the mass knee from the accuracy knee

NET-36, cell B (`d = 4`, `ctx = 512`, seed 2): reported effective support
`N_eff = 152.11`, reported accuracy knee `k* = 64` at retention threshold `0.98`.
Cell A (`d = 16`, `ctx = 128`, seed 1): `N_eff = 52.73`, `k* = 64`.
-/




/-!
### The spike family: small effective support, stubborn top-`k` mass
-/















open AttentionConcentration in
theorem solution(s T : Finset ι) (p : ι → ℝ) (hT : T ⊆ s)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i ∈ T, p i ≤ Real.sqrt (T.card * collision s p) := by
  have hnn : 0 ≤ ∑ i ∈ T, p i :=
    Finset.sum_nonneg fun i hi => hp i (hT hi)
  have := sq_subset_mass_le s T p hT
  calc ∑ i ∈ T, p i = Real.sqrt ((∑ i ∈ T, p i) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (T.card * collision s p) := Real.sqrt_le_sqrt this
