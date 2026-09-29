-- Prove2me | Theorems.Thm_mme_finset_pointwise_one_eighth_aggregate_nonholes
-- name    : mme_finset_pointwise_one_eighth_aggregate_nonholes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:23:49.652085+00:00
-- url     : https://prove2.me/theorems/0ed555e8-cbdb-42c3-bab0-6eb76401a74e
-- title:
--   Pointwise one-eighth bad-event bounds give seven-eighths aggregate nonhole mass
-- statement:
--   Let $W$ be a finite set of hash weights and $B$ a finite set of blocks. For each block $z$, let $\operatorname{Bad}(z)\subseteq W$ be its bad-weight set. If every block is bad for at most one eighth of the weights,
--
--   $$
--   8\,|\operatorname{Bad}(z)|\le |W| \qquad (z\in B),
--   $$
--
--   then the total number of nonbad block--weight incidences satisfies
--
--   $$
--   7|W||B|\le 8\sum_{w\in W}|\{z\in B:w\notin\operatorname{Bad}(z)\}|.
--   $$
--
--   This division-free double-counting form includes empty finite sets. It is the aggregate expectation step that converts the pointwise hole-probability estimate in Claim 6.8 into the summed nonhole mass used before the Hole Lemma and Equation (24).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8 and its aggregate use immediately before Equation (24), printed pp. 56--57 (PDF pp. 57--58), https://arxiv.org/abs/2210.10173

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open BigOperators

set_option autoImplicit false

theorem mme_finset_pointwise_one_eighth_aggregate_nonholes
    {Weight Block : Type}
    [Fintype Weight] [Fintype Block]
    [DecidableEq Weight] [DecidableEq Block]
    (bad : Block → Weight → Prop) [DecidableRel bad]
    (hpointwise : ∀ z : Block,
      8 * (Finset.univ.filter (bad z)).card ≤ Fintype.card Weight) :
    7 * Fintype.card Weight * Fintype.card Block ≤
      8 * ∑ w : Weight,
        (Finset.univ.filter (fun z : Block ↦ ¬ bad z w)).card := by
  sorry
