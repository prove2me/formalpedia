-- Prove2me | solution 1 for Logic.JFeature.enrich_marginal_feature_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:10:26.166993+00:00
-- url     : https://prove2.me/submissions/397fb16b-e97a-46f7-a827-fec7aac88112

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

omit [DecidableEq α] [DecidableEq β] in
/-- Any first-coordinate feature cell is a `rowSet`. -/
lemma filter_fst_eq_rowSet {κ : Type*} [DecidableEq κ] (u : α → κ) (k : κ) :
    (univ.filter (fun x : α × β => u x.1 = k)) = rowSet (univ.filter (fun a => u a = k)) := by
  ext x; simp [rowSet, Finset.mem_product]


omit [Fintype α] in
/-- **Row-balanced hit counting.** A row-balanced hit set puts exactly `m` hits
into each row of a cell, whatever the cell. -/
lemma card_inter_rowSet {H : Finset (α × β)} {m : ℕ} (hH : RowBalanced H m) (S : Finset α) :
    (H ∩ rowSet (β := β) S).card = S.card * m := by
  rw [card_inter_rowSet_sum]
  rw [Finset.sum_congr rfl (fun a _ => hH a), Finset.sum_const, smul_eq_mul]

omit [Fintype α] in
/-- **Marginal blindness, rate form.** For a row-balanced hit set, *every* cell
cut out by *any* feature of the first coordinate has hit rate `m / card β`,
independently of the feature and of the cell.  No such feature can ever show an
enrichment. -/
theorem rate_rowSet [Nonempty β] {H : Finset (α × β)} {m : ℕ} (hH : RowBalanced H m)
    {S : Finset α} (hS : S.Nonempty) :
    rate H (rowSet S) = (m : ℝ) / (Fintype.card β : ℝ) := by
  have hScard : ((S.card : ℝ)) ≠ 0 := by
    have : 0 < S.card := Finset.card_pos.2 hS
    positivity
  rw [rate, card_inter_rowSet hH, card_rowSet]
  push_cast
  exact mul_div_mul_left _ _ hScard

/-- **Marginal blindness, enrichment form.** Every marginal cell has enrichment
ratio exactly `1`.  (`0 < m` rules out the degenerate empty-hit case, where the
ratio is a `0/0`.) -/
theorem enrich_rowSet_eq_one [Nonempty β] {H : Finset (α × β)} {m : ℕ}
    (hH : RowBalanced H m) (hm : 0 < m) {S : Finset α} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    enrich H (rowSet S) = 1 := by
  have hne : (m : ℝ) / (Fintype.card β : ℝ) ≠ 0 := by
    have h1 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    have h2 : (0:ℝ) < (Fintype.card β : ℝ) := by
      have : 0 < Fintype.card β := Fintype.card_pos
      exact_mod_cast this
    positivity
  rw [enrich, compl_rowSet, rate_rowSet hH hS, rate_rowSet hH hSc, div_self hne]




/-! ### A carrier that hides from every marginal feature -/









open Logic.JFeature in
theorem solution[Nonempty β] {κ : Type*} [DecidableEq κ]
    {H : Finset (α × β)} {m : ℕ} (hH : RowBalanced H m) (hm : 0 < m) (u : α → κ) (k : κ)
    (hS : (univ.filter (fun a => u a = k)).Nonempty)
    (hSc : (univ.filter (fun a => u a = k))ᶜ.Nonempty) :
    enrich H (univ.filter (fun x : α × β => u x.1 = k)) = 1 := by
  rw [filter_fst_eq_rowSet]
  exact enrich_rowSet_eq_one hH hm hS hSc
