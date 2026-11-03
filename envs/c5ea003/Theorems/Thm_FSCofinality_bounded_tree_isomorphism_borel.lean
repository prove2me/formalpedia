-- Prove2me | Theorems.Thm_FSCofinality_bounded_tree_isomorphism_borel
-- name    : FSCofinality.bounded_tree_isomorphism_borel
-- status  : Proved
-- author  : @username
-- created : 2026-11-02T12:40:00.192986+00:00
-- url     : https://prove2.me/theorems/9f8184f7-ba41-4d9c-a4a6-4052986ae7f5
-- title:
--   Friedman--Stanley: Borelness of bounded-rank tree isomorphism
-- statement:
--   For each countable ordinal a, isomorphism of the rooted tree codes with global reverse-tree height at most a is a Borel subset of the product of that bounded-tree measurable space with itself. Empty and finite trees are included and branch multiplicities are retained. This is the classical bounded-rank Borelness result used in the hierarchy comparison; it does not assert Borelness of isomorphism on all well-founded or all countable trees at once.
--
--   For every $\alpha<\omega_1$, with $\mathfrak T_\alpha$ carrying the inherited measurable structure, $$\{(T,U)\in\mathfrak T_\alpha^2:T\cong U\}\text{ is Borel}.$$
-- source:
--   H. Friedman and L. Stanley, A Borel reducibility theory for classes of countable structures, Journal of Symbolic Logic 54 (1989), 894--914, https://doi.org/10.2307/2274750, Section 1.2.1, pages 901--902 (Borelness via multiplicity codes). Also supplied draft, Proposition 4.15 proof.

import Definitions.Def_FSCofinalityTrees20261102
import Definitions.Def_FSCofinalityHierarchy20261102

set_option autoImplicit false

theorem FSCofinality.bounded_tree_isomorphism_borel
    (a : Ordinal.{0}) (ha_countable : a < Ordinal.omega 1) :
    @MeasurableSet
      ((FSCofinality.RootedTrees.treeRelation a).Carrier ×
        (FSCofinality.RootedTrees.treeRelation a).Carrier)
      ((FSCofinality.RootedTrees.treeRelation a).measurableSpace.prod
        (FSCofinality.RootedTrees.treeRelation a).measurableSpace)
      {p | (FSCofinality.RootedTrees.treeRelation a).rel p.1 p.2} := by sorry
