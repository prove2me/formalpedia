-- Prove2me | Definitions.Def_Novelty_AdaptiveMenuCapacity
-- name    : Novelty_AdaptiveMenuCapacity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:00:24.691285+00:00
-- url     : https://prove2.me/theorems/648edac8-1516-45e3-b530-8d97b81e5f5f
-- title:
--   Aether Catalog definitions — Novelty_AdaptiveMenuCapacity
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AdaptiveMenuCapacity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AdaptiveMenuCapacity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_StatisticRealizationBound

/-!
# Cycle 3: adaptive query policies cannot beat menu indistinguishability

Cycles 1–2 priced the oracle navigation sensor and showed that *static* residue policies realize
none of it.  The laboratory's strongest policies were **adaptive** (`ADAPTIVE-NB`), choosing the
next query in the light of earlier answers, so a complete account must cover adaptivity.

This file models an adaptive policy as a decision tree whose internal nodes are queries drawn
from a menu `M` of Boolean functions of the sample, and proves that adaptivity buys nothing
against indistinguishability: two samples that agree on every menu query receive the *same*
answer from every tree over that menu, of any depth, however it was fitted.  Instantiated at the
navigation sensor this yields: for every modulus `L` and threshold `B`, every adaptive residue
policy errs on one of two explicit semiprimes.

## Main results

* `QueryTree.eval_eq_of_menu_agree` : menu-indistinguishable samples get equal answers from any
  tree over the menu (induction on the tree);
* `QueryTree.errs_of_menu_agree` : hence every such tree errs on one of a pair whose target
  values differ;
* `QueryTree.numLeaves_le_two_pow_depth` : a depth-`k` tree has at most `2 ^ k` leaves, so it is
  measurable with respect to a statistic with at most `2 ^ k` classes — the capacity reading of
  the crediting law of `Novelty.StatisticRealizationBound`;
* `adaptive_residue_policy_errs` : the navigation-sensor instance — no adaptive residue policy,
  of any depth, matches the sensor on the whole semiprime population.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): adaptivity is irrelevant to the realization gap, because the gap is
caused by the *information* in the menu, not by the order in which it is read.

Experiment (Experimenter): the pair produced by `residue_menu_blind` (a prime square `p²` and a
semiprime `p·q₂` with `q₂ ≡ p mod L`) has identical residues modulo `L` and opposite sensor
values; every decision tree over residue queries therefore has accuracy exactly `1/2` on it —
the two-point analogue of the measured "strict crediting `0 %`".

Analysis (Analyst): the induction is short because indistinguishability propagates through the
branch: both samples take the same branch at every node.  This is the structural reason a
`z`-score of `+118` pooled can coexist with `z ≤ 2.3` within strata: pooling changes the target,
not the information.

Critique (Critic): a decision tree is the right model only if queries are deterministic
functions of the sample; randomized policies are not covered and would need an averaging
argument.  The depth bound is stated separately from the error bound, since the error bound
holds at *every* depth — including depth exceeding the menu size.
-/

namespace AdaptiveMenu

/-- An adaptive query policy: a decision tree whose nodes are Boolean queries. -/
inductive QueryTree (ι : Type*) where
  | leaf : Bool → QueryTree ι
  | node : (ι → Bool) → QueryTree ι → QueryTree ι → QueryTree ι

namespace QueryTree

variable {ι : Type*}

/-- Running the policy on a sample. -/
def eval : QueryTree ι → ι → Bool
  | leaf b, _ => b
  | node m t f, i => if m i then eval t i else eval f i

/-- All queries of the tree come from the menu `M`. -/
def Uses (M : Set (ι → Bool)) : QueryTree ι → Prop
  | leaf _ => True
  | node m t f => m ∈ M ∧ Uses M t ∧ Uses M f

/-- The number of leaves of the tree. -/
def numLeaves : QueryTree ι → ℕ
  | leaf _ => 1
  | node _ t f => numLeaves t + numLeaves f

/-- The depth of the tree. -/
def depth : QueryTree ι → ℕ
  | leaf _ => 0
  | node _ t f => max (depth t) (depth f) + 1




end QueryTree

open OracleRealizationGap

/-- The residue menu modulo `L`: all queries "is `N ≡ r` mod `L`?" of the sample's value. -/
def residueMenu (L : ℕ) : Set (ℕ × ℕ → Bool) :=
  {m | ∃ r : ℕ, m = fun x => decide ((x.1 * x.2) % L = r)}


end AdaptiveMenu


