-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:40:12.95066+00:00
-- url     : https://prove2.me/theorems/fc2b2b43-eb78-414a-81c4-91d89c6ef026
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A maximal graph under the attached planar-drawing predicate, on at least three vertices, has at least 3|V|−6 edges. The proof route is to extend any planar simple graph with fewer edges to a maximal planar supergraph and use triangulation/Euler counting; maximality then identifies that supergraph with K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
