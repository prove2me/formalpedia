-- Prove2me | Theorems.Thm_SelectionExchange_exists_half_subset
-- name    : SelectionExchange.exists_half_subset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:45:11.890062+00:00
-- url     : https://prove2.me/theorems/b92c5063-4bd3-4aac-b83b-ff8eee383528
-- title:
--   Half of a set carries half of its mass.
-- statement:
--   **Half of a set carries half of its mass.**  In any set `E` of `2m` positions there
--   are `m` positions carrying at least half the total weight: take a maximiser among the
--   `m`-subsets; its complement inside `E` has the same size, hence no larger weight.
--
--   ```lean
--   theorem SelectionExchange.exists_half_subset(p : ι → ℝ) (E : Finset ι) (m : ℕ) (hE : E.card = 2 * m) :
--       ∃ C ⊆ E, C.card = m ∧ ∑ i ∈ E, p i ≤ 2 * ∑ i ∈ C, p i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AttentionSelectionExchange.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AttentionSelectionExchange.lean#L56

-- Thm stub generated from Logic/AttentionSelectionExchange.lean
import Mathlib
import Definitions.Def_Logic_AttentionSelectionDilution
import Definitions.Def_Logic_AttentionSelectionExchange
/-
# The exchange theorem: self-similar refinement preserves the selection gap **exactly**
# (NET-45, cycle 2)

`Logic.AttentionSelectionDilution` proves one half of the dilution theorem: under the
self-similar refinement `split p` of an attention profile (each position replaced by two
positions of half its weight) the top-`2k` mass is *at least* the old top-`k` mass, so the
selection gap cannot decrease.  The inequality was cheap — the refined pruner can always
copy the old selection.

This file proves the converse, which is not cheap: **the refined pruner can do no
better**.  The obstruction is that a `2k`-subset of the refined context need not be a
union of split pairs: it may take one half of some positions and both halves of others,
i.e. it solves a *fractional* selection problem with weights in `{1/2, 1}`.  The theorem
says that this relaxation buys nothing.

**The exchange argument.**  Write a subset `U ⊆ ι × Bool` through its two traces
`S_true, S_false ⊆ ι`.  Then `2 · mass(U) = ∑_{S_true} p + ∑_{S_false} p
= 2 ∑_{D} p + ∑_{E} p`, where `D = S_true ∩ S_false` are the doubly-selected positions and
`E` is the symmetric difference, and `2|D| + |E| = |U| = 2k`.  The set `E` has *even*
cardinality `2(k - |D|)`, and `SelectionExchange.exists_half_subset` — the combinatorial
core — produces a subset `C ⊆ E` of exactly half the size carrying at least half the
mass, by taking a maximiser: its complement inside `E` has the same cardinality, hence no
larger mass.  Then `D ∪ C` has exactly `k` elements and `mass(U) ≤ ∑_{D ∪ C} p ≤ T_k`.
No positivity, ordering, or normalisation of the profile is used.

**Results.**

* `SelectionExchange.exists_half_subset` : in any set of `2m` positions some `m` of them
  carry at least half the mass.  (A maximiser argument; true for signed weights.)
* `SelectionExchange.topMass_split_le`, `topMass_split_eq` : the top-mass functional is
  **invariant** under self-similar refinement at the matched budget:
  `T_{2k}(split p) = T_k(p)`.
* `SelectionExchange.selection_gap_split_eq` : hence the selection gap is *exactly*
  invariant, upgrading `SelectionDilution.selection_gap_mono_under_self_similar_refinement`
  from an inequality to an equality.
* `SelectionExchange.gap_change_refutes_self_similarity` : consequently **any** measured
  change of the selection gap across a context doubling at matched sparsity — in either
  direction — refutes exact self-similarity of the attention profile.  NET-45's decay
  `+5.9 → +1.7` is therefore a two-sided falsification, not merely a bound.
* `SelectionExchange.net45_gap_change_is_strict` : the round's own numbers are a strict
  change, so the hypothesis of the refutation is met by the measurement.
-/


open SelectionExchange

open Finset SelectionDilution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1.  The combinatorial core -/

omit [Fintype ι] in

theorem SelectionExchange.exists_half_subset(p : ι → ℝ) (E : Finset ι) (m : ℕ) (hE : E.card = 2 * m) :
    ∃ C ⊆ E, C.card = m ∧ ∑ i ∈ E, p i ≤ 2 * ∑ i ∈ C, p i := by sorry
