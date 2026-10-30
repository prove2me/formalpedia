-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_2a77893c_8379_4827_8265_76a9c861f3f2
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count_2a77893c_8379_4827_8265_76a9c861f3f2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:33:39.280091+00:00
-- url     : https://prove2.me/theorems/e6187372-db43-4b05-9178-6f8ead22bdbc
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable graphs on the same vertex set has exactly 3|V| − 6 edges. The vertex lower bound includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count_2a77893c_8379_4827_8265_76a9c861f3f2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
