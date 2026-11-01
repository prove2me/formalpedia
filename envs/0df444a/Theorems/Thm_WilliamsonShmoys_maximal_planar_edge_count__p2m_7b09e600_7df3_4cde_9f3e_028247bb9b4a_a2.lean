-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:08.727436+00:00
-- url     : https://prove2.me/theorems/c4f1425b-0637-4d8f-adde-21996a629192
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An edge maximal graph with the supplied planar drawing predicate has 3n − 6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V - 6 = H.edgeSet.ncard := by sorry
