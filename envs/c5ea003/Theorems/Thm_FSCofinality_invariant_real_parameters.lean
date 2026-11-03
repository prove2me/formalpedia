-- Prove2me | Theorems.Thm_FSCofinality_invariant_real_parameters
-- name    : FSCofinality.invariant_real_parameters
-- status  : Proved
-- author  : @username
-- created : 2026-11-02T12:40:29.891458+00:00
-- url     : https://prove2.me/theorems/5791fd93-6a01-4c48-8992-81bc70de0871
-- title:
--   Proposition 3.6 — invariant real parameters of countable graphs
-- statement:
--   Let h map simple countable graphs Borelly into Cantor space and be constant on graph-isomorphism classes. Then there exist one real r and a Borel self-reduction g of graph isomorphism such that h(g(G))=r for every graph G. A self-reduction preserves and reflects graph isomorphism on all pairs. No uniform dependence on h is required. The conclusion places a copy of the entire graph-isomorphism problem inside one invariant real-parameter fiber.
--
--   Writing $\mathrm{Graph}$ for the specified graph space, the conclusion is $$\exists r\in2^{\mathbb N}\ \exists g:\mathrm{Graph}\to\mathrm{Graph}\quad [g\text{ is a Borel reduction}]\ \land\ \forall G,\ h(g(G))=r.$$ The map $h$ is assumed Borel and constant on graph-isomorphism classes.
-- source:
--   Friedman--Stanley cofinality and Borel completeness: A proposed negative answer to the Friedman--Stanley question, supplied research draft dated 2 November 2026, FriedmanStanleyQuestion.tex, Proposition 3.6 (Invariant real parameters), lines 719--752.

import Definitions.Def_FSCofinalityStructures20261102

set_option autoImplicit false

theorem FSCofinality.invariant_real_parameters
    (h : FSCofinality.GraphSpace → (ℕ → Bool)) (h_borel : Measurable h)
    (h_invariant : ∀ G H, FSCofinality.GraphIsomorphic G H → h G = h H) :
    ∃ r : ℕ → Bool, ∃ g : FSCofinality.GraphSpace → FSCofinality.GraphSpace,
      Measurable g ∧
      (∀ G H, FSCofinality.GraphIsomorphic G H ↔
        FSCofinality.GraphIsomorphic (g G) (g H)) ∧
      ∀ G, h (g G) = r := by sorry
