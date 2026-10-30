-- Prove2me | Theorems.Thm_exists_maximal_simpleGraph_supergraph_of_finite__p2m_4cee4fb6_81c0_44bc_ba4b_b191f8c55242_a1
-- name    : exists_maximal_simpleGraph_supergraph_of_finite__p2m_4cee4fb6_81c0_44bc_ba4b_b191f8c55242_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:40.641288+00:00
-- url     : https://prove2.me/theorems/e5f2fc71-b600-483a-88dd-fc5a11021398
-- title:
--   Finite maximality for simple graph extensions
-- statement:
--   For any finite vertex type and any property P of simple graphs, if L has property P, then L has an extension M with property P that has no proper P extension on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem exists_maximal_simpleGraph_supergraph_of_finite__p2m_4cee4fb6_81c0_44bc_ba4b_b191f8c55242_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) (P : SimpleGraph V → Prop) (hL : P L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ P M ∧
      ∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M := by
  sorry
