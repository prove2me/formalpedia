-- Prove2me | solution 1 for Logic.JFeature.exists_fiber_rate_ge_globalRate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:10:27.340625+00:00
-- url     : https://prove2.me/submissions/167e15f9-d12e-49da-a8d8-b7389d883647

-- Sol generated from Logic/JFeatureMarginalBlindness.lean
import Mathlib
import Definitions.Def_Logic_JFeatureMarginalBlindness
/-
# Marginal blindness: why no `j`-feature can carry a hidden pair-carrier

This file formalises the structural reason behind the empirical verdict
`H0_CARRIER_OPEN` of the j-feature sweep (paper 248): *eight* registered
families of arithmetic features of the position index `j`
(`j mod 4`, `j mod 3`, `j mod 5`, `j mod 7`, `j mod 105`, `omega_small(j)`
terciles, smoothness of `|j - nearest square|`, `10^6`-smoothness of `j`)
all returned honest enrichment ratios `R ≤ 1.11`.

The theorems below say that this is not an accident of the particular eight
features chosen: on a sample space `α × β` where the hit set is *row balanced*
(every value of the first coordinate carries the same number of hits), **every**
cell cut out by **any** function of the first coordinate has enrichment ratio
*exactly* `1`.  Whatever new feature of `j` one invents, the marginal sweep is
guaranteed to return `R = 1`; the sweep has no power at all against carriers
that live in the *joint* (consecutive-position) structure.

Yet such carriers exist and are arbitrarily strong: for the graph of a
permutation `σ : α ≃ β` (a row-balanced hit set with one hit per row) the joint
cell "the graph itself" has hit rate `1`, i.e. enrichment `card α` over the
global rate, while all marginal cells sit at exactly `1`.

Main results.

* `exists_fiber_hits_ge` / `exists_fiber_rate_ge_globalRate` : the *selection
  floor*.  For every feature map and every hit set there is always a nonempty
  cell whose hit rate is at least the global rate; a raw "max over cells of
  `R`" statistic is therefore `≥ 1` by pure pigeonhole, with no signal
  whatsoever.  (Used in `Logic.JFeatureMaxStatistic` to show that the
  uncalibrated max test has type-I error rate `1`.)
* `rate_rowSet`, `enrich_rowSet_eq_one`, `enrich_marginal_feature_eq_one` :
  **marginal blindness**.
* `graphFinset_rowBalanced`, `rate_graphFinset`,
  `graph_joint_rate_eq_card_mul_globalRate`,
  `marginal_blind_carrier` : the joint carrier that is invisible to every
  marginal feature, with unbounded joint enrichment.
-/

open Logic.JFeature

open Finset

/-! ## Hit rates, global rate, enrichment -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]










/-! ## The selection floor: some cell always looks enriched -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]


omit [Fintype κ] in
lemma inter_filter_eq (u : ι → κ) (H : Finset ι) (k : κ) :
    H ∩ (univ.filter (fun i => u i = k)) = H.filter (fun i => u i = k) := by
  ext x; simp [Finset.mem_inter, Finset.mem_filter]



/-! ## Marginal blindness on a product sample space -/


variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]














/-! ### A carrier that hides from every marginal feature -/









open Logic.JFeature in
theorem solution[Nonempty ι] (u : ι → κ) (H : Finset ι) :
    ∃ k : κ, (univ.filter (fun i => u i = k)).Nonempty ∧
      globalRate H ≤ rate H (univ.filter (fun i => u i = k)) := by
  classical
  set F : κ → Finset ι := fun k => univ.filter (fun i => u i = k) with hF
  set Hf : κ → Finset ι := fun k => H.filter (fun i => u i = k) with hHf
  have hn : (0:ℝ) < (Fintype.card ι : ℝ) := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast this
  have hsumH : ∑ k : κ, (Hf k).card = H.card :=
    (Finset.card_eq_sum_card_fiberwise (f := u) (s := H) (t := univ)
      (fun x _ => Finset.mem_univ _)).symm
  have hsumU : ∑ k : κ, (F k).card = Fintype.card ι := by
    have := (Finset.card_eq_sum_card_fiberwise (f := u) (s := (univ : Finset ι))
      (t := univ) (fun x _ => Finset.mem_univ _)).symm
    simpa [hF, Finset.card_univ] using this
  by_contra hcon
  push_neg at hcon
  -- every nonempty fiber is strictly under-represented
  have key : ∀ k : κ, (Hf k).card * Fintype.card ι ≤ H.card * (F k).card := by
    intro k
    by_cases hne : (F k).Nonempty
    · have hlt := hcon k hne
      have hFk : (0:ℝ) < ((F k).card : ℝ) := by
        have : 0 < (F k).card := Finset.card_pos.2 hne
        exact_mod_cast this
      have : ((Hf k).card : ℝ) * (Fintype.card ι : ℝ) < (H.card : ℝ) * ((F k).card : ℝ) := by
        have h2 : ((Hf k).card : ℝ) / ((F k).card : ℝ) < (H.card : ℝ) / (Fintype.card ι : ℝ) := by
          simpa [rate, globalRate, hHf, hF, inter_filter_eq] using hlt
        rw [div_lt_div_iff₀ hFk hn] at h2
        linarith
      exact_mod_cast this.le
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 : Hf k = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        have hx' : x ∈ F k := by
          simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (Finset.mem_filter.1 hx).2
        rw [hne] at hx'
        exact absurd hx' (Finset.notMem_empty x)
      simp [h0, hne]
  -- but at the fiber of an actual point the inequality is strict
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hne0 : (F (u i₀)).Nonempty := ⟨i₀, by simp [hF]⟩
  have hstrict : (Hf (u i₀)).card * Fintype.card ι < H.card * (F (u i₀)).card := by
    have hlt := hcon (u i₀) hne0
    have hFk : (0:ℝ) < ((F (u i₀)).card : ℝ) := by
      have : 0 < (F (u i₀)).card := Finset.card_pos.2 hne0
      exact_mod_cast this
    have : ((Hf (u i₀)).card : ℝ) * (Fintype.card ι : ℝ)
        < (H.card : ℝ) * ((F (u i₀)).card : ℝ) := by
      have h2 : ((Hf (u i₀)).card : ℝ) / ((F (u i₀)).card : ℝ)
          < (H.card : ℝ) / (Fintype.card ι : ℝ) := by
        simpa [rate, globalRate, hHf, hF, inter_filter_eq] using hlt
      rw [div_lt_div_iff₀ hFk hn] at h2
      linarith
    exact_mod_cast this
  have hsum : ∑ k : κ, (Hf k).card * Fintype.card ι
      < ∑ k : κ, H.card * (F k).card :=
    Finset.sum_lt_sum (fun k _ => key k) ⟨u i₀, Finset.mem_univ _, hstrict⟩
  rw [← Finset.sum_mul, hsumH, ← Finset.mul_sum, hsumU] at hsum
  omega
