-- Prove2me | Theorems.Thm_AdaptiveMenu_adaptive_residue_policy_errs
-- name    : AdaptiveMenu.adaptive_residue_policy_errs
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T14:57:19.421785+00:00
-- url     : https://prove2.me/theorems/76ad1ac9-27ed-4da8-8966-d968470a1b26
-- title:
--   No adaptive residue policy realizes the navigation sensor.
-- statement:
--   **No adaptive residue policy realizes the navigation sensor.**  For every modulus `L ≠ 0`
--   and threshold `B` there are two semiprimes on which every adaptive policy built from residue
--   queries — of any depth, however fitted — makes a mistake.
--
--   ```lean
--   theorem AdaptiveMenu.adaptive_residue_policy_errs(L B : ℕ) (hL : L ≠ 0) :
--       ∃ p q₁ q₂ : ℕ, p.Prime ∧ q₁.Prime ∧ q₂.Prime ∧ q₁ ≠ q₂ ∧
--         ∀ t : QueryTree (ℕ × ℕ), t.Uses (residueMenu L) →
--           t.eval (p, q₁) ≠ sensor B p q₁ ∨ t.eval (p, q₂) ≠ sensor B p q₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AdaptiveMenuCapacity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AdaptiveMenuCapacity.lean#L123

-- Thm stub generated from Novelty/AdaptiveMenuCapacity.lean
import Mathlib
import Definitions.Def_Novelty_AdaptiveMenuCapacity
import Definitions.Def_Novelty_OracleRealizationGap
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

open AdaptiveMenu


open QueryTree

variable {ι : Type*}









open OracleRealizationGap

theorem AdaptiveMenu.adaptive_residue_policy_errs(L B : ℕ) (hL : L ≠ 0) :
    ∃ p q₁ q₂ : ℕ, p.Prime ∧ q₁.Prime ∧ q₂.Prime ∧ q₁ ≠ q₂ ∧
      ∀ t : QueryTree (ℕ × ℕ), t.Uses (residueMenu L) →
        t.eval (p, q₁) ≠ sensor B p q₁ ∨ t.eval (p, q₂) ≠ sensor B p q₂ := by sorry
