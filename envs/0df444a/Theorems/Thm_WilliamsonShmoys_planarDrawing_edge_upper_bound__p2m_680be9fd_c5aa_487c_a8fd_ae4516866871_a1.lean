-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_upper_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1
-- name    : WilliamsonShmoys.planarDrawing_edge_upper_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:40:15.473384+00:00
-- url     : https://prove2.me/theorems/82c54c31-7f79-42ee-8f08-de4d2157b6b0
-- title:
--   Planar drawing edge upper bound
-- statement:
--   For a finite simple graph with at least three vertices that has a drawing satisfying the attached crossing-free arc definition, the number of edges is at most 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_edge_upper_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
