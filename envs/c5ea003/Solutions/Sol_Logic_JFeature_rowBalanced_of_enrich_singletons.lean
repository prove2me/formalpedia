-- Prove2me | solution 1 for Logic.JFeature.rowBalanced_of_enrich_singletons
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:11:55.007892+00:00
-- url     : https://prove2.me/submissions/50187d6d-3def-4957-a2c8-2899995007e7

-- Sol generated from Logic/JFeatureMarginalBlindness.lean
import Mathlib
import Definitions.Def_Logic_JFeatureMarginalBlindness
import Theorems.Thm_Logic_JFeature_card_inter_rowSet_sum
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





/-! ## Marginal blindness on a product sample space -/


variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]




omit [Fintype α] [DecidableEq α] [DecidableEq β] in
lemma card_rowSet (S : Finset α) :
    (rowSet (β := β) S).card = S.card * Fintype.card β := by
  simp [rowSet, Finset.card_product, Finset.card_univ]

lemma compl_rowSet (S : Finset α) : (rowSet (β := β) S)ᶜ = rowSet Sᶜ := by
  ext x; simp [rowSet, Finset.mem_product]









/-! ### A carrier that hides from every marginal feature -/









open Logic.JFeature in
theorem solution[Nonempty β] {H : Finset (α × β)}
    (hcard : 2 ≤ Fintype.card α)
    (h : ∀ a : α, enrich H (rowSet ({a} : Finset α)) = 1) :
    ∃ m : ℕ, RowBalanced H m ∧ H.card = Fintype.card α * m := by
  classical
  have hb : (0:ℝ) < (Fintype.card β : ℝ) := by
    have : 0 < Fintype.card β := Fintype.card_pos
    exact_mod_cast this
  have hnR : (2:ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hcard
  have htot : ∑ b : α, rowHits H b = H.card := by
    have hru : rowSet (β := β) (univ : Finset α) = (univ : Finset (α × β)) := by
      ext x; simp [rowSet]
    have := card_inter_rowSet_sum H (univ : Finset α)
    rw [hru, Finset.inter_univ] at this
    exact this.symm
  have key : ∀ a : α, Fintype.card α * rowHits H a = H.card := by
    intro a
    have hsum : rowHits H a + ∑ b ∈ ({a} : Finset α)ᶜ, rowHits H b = H.card := by
      have h0 : ∑ b ∈ ({a} : Finset α), rowHits H b
          + ∑ b ∈ ({a} : Finset α)ᶜ, rowHits H b = ∑ b : α, rowHits H b :=
        Finset.sum_add_sum_compl _ _
      rw [Finset.sum_singleton] at h0
      rw [h0, htot]
    have hcardC : (rowSet (β := β) ({a} : Finset α)).card = Fintype.card β := by
      rw [card_rowSet, Finset.card_singleton, one_mul]
    have hA : rate H (rowSet (β := β) ({a} : Finset α))
        = (rowHits H a : ℝ) / (Fintype.card β : ℝ) := by
      rw [rate, card_inter_rowSet_sum, hcardC, Finset.sum_singleton]
    have hcardCc : (rowSet (β := β) (({a} : Finset α)ᶜ)).card
        = (Fintype.card α - 1) * Fintype.card β := by
      rw [card_rowSet, Finset.card_compl, Finset.card_singleton]
    have hB : rate H (rowSet (β := β) (({a} : Finset α)ᶜ))
        = ((∑ b ∈ ({a} : Finset α)ᶜ, rowHits H b : ℕ) : ℝ)
          / (((Fintype.card α - 1) * Fintype.card β : ℕ) : ℝ) := by
      rw [rate, card_inter_rowSet_sum, hcardCc]
    have hne : rate H (rowSet (β := β) ({a} : Finset α))ᶜ ≠ 0 := by
      intro h0
      have h1 := h a
      rw [enrich, h0, div_zero] at h1
      exact zero_ne_one h1
    have hAB : rate H (rowSet (β := β) ({a} : Finset α))
        = rate H (rowSet (β := β) ({a} : Finset α))ᶜ := by
      have h1 := h a
      rw [enrich, div_eq_one_iff_eq hne] at h1
      exact h1
    rw [compl_rowSet, hA, hB] at hAB
    -- clear denominators
    have hcast : (((Fintype.card α - 1) * Fintype.card β : ℕ) : ℝ)
        = ((Fintype.card α : ℝ) - 1) * (Fintype.card β : ℝ) := by
      have h1 : (1:ℕ) ≤ Fintype.card α := by omega
      push_cast [Nat.cast_sub h1]
      ring
    rw [hcast] at hAB
    have hpos : (0:ℝ) < ((Fintype.card α : ℝ) - 1) * (Fintype.card β : ℝ) := by
      have : (0:ℝ) < (Fintype.card α : ℝ) - 1 := by linarith
      positivity
    rw [div_eq_div_iff (ne_of_gt hb) (ne_of_gt hpos)] at hAB
    have hsumR : (rowHits H a : ℝ) + ((∑ b ∈ ({a} : Finset α)ᶜ, rowHits H b : ℕ) : ℝ)
        = (H.card : ℝ) := by exact_mod_cast hsum
    have hfinal : (Fintype.card α : ℝ) * (rowHits H a : ℝ) = (H.card : ℝ) := by
      nlinarith [hAB, hsumR]
    exact_mod_cast hfinal
  have hneα : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨a₀⟩ := hneα
  refine ⟨rowHits H a₀, ?_, ?_⟩
  · intro a
    have h1 := key a
    have h2 := key a₀
    have hn : 0 < Fintype.card α := by omega
    have : Fintype.card α * rowHits H a = Fintype.card α * rowHits H a₀ := by
      rw [h1, h2]
    exact Nat.eq_of_mul_eq_mul_left hn this
  · exact (key a₀).symm
