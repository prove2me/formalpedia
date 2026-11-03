-- Prove2me | Theorems.Thm_FSCofinality_original_tree_comparison
-- name    : FSCofinality.original_tree_comparison
-- status  : Proved
-- author  : @username
-- created : 2026-11-02T12:41:33.798836+00:00
-- url     : https://prove2.me/theorems/462343aa-6d61-4a82-aeec-4dc0fb9ffe39
-- title:
--   Proposition 4.15 — original tree hierarchy compared with the set-jump tower
-- statement:
--   For every nonzero countable ordinal a, there is a countable ordinal b such that isomorphism on the bounded-rank rooted tree class at bound a Borel reduces to the product-limit Friedman--Stanley relation J_b. Empty and finite trees and all branch multiplicities are included. This formalizes the first assertion of Proposition 4.15; no equality of the indices a and b, and no simultaneous Borel choice over ordinal codes, is asserted. The separate structural sentence-tower assertion is outside this milestone.
--
--   The comparison has independently quantified countable indices: $$\forall\,0<\alpha<\omega_1\ \exists\beta<\omega_1,\qquad \cong_{\mathfrak T_\alpha}\leq_B\mathsf J_\beta.$$
-- source:
--   Friedman--Stanley cofinality and Borel completeness: A proposed negative answer to the Friedman--Stanley question, supplied research draft dated 2 November 2026, FriedmanStanleyQuestion.tex, Proposition 4.15, first assertion, lines 1701--1740; original tree codes: Friedman--Stanley (1989), Section 1.2.1, page 901.

import Definitions.Def_FSCofinalityHierarchy20261102
import Definitions.Def_FSCofinalityTrees20261102

set_option autoImplicit false

theorem FSCofinality.original_tree_comparison
    (a : Ordinal.{0}) (ha_pos : 0 < a) (ha_countable : a < Ordinal.omega 1) :
    ∃ b : Ordinal.{0}, b < Ordinal.omega 1 ∧
      (FSCofinality.RootedTrees.treeRelation a).Reduces (FSCofinality.fsTower b) := by sorry
