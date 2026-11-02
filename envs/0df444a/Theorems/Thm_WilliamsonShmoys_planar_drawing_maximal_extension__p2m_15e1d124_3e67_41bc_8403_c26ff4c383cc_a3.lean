-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_15e1d124_3e67_41bc_8403_c26ff4c383cc_a3
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_15e1d124_3e67_41bc_8403_c26ff4c383cc_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:26:07.102035+00:00
-- url     : https://prove2.me/theorems/696fd018-9619-40b1-ac8f-a50109776ace
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that is maximal under graph inclusion, with edge count at least that of the original graph. The proof route is to maximize edge count over the finite set of drawable supergraphs containing the input graph. This step works without a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_15e1d124_3e67_41bc_8403_c26ff4c383cc_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) :
    ∃ M : SimpleGraph V,
      U ≤ M ∧ HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) ∧
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       U.edgeFinset.card ≤ M.edgeFinset.card) := by sorry
