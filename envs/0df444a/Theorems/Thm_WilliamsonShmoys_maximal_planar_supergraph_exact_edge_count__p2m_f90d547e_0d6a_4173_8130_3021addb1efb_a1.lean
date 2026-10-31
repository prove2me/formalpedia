-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exact_edge_count__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exact_edge_count__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:36:28.878662+00:00
-- url     : https://prove2.me/theorems/3e16b919-4c6f-4ffa-b173-33b0ad744e42
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on at least three finite vertices has exactly 3n−6 edges, by triangulating its faces and applying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_exact_edge_count__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet = M.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
