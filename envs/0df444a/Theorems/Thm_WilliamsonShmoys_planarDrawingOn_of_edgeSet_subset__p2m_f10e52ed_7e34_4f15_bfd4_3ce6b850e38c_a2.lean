-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_of_edgeSet_subset__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2
-- name    : WilliamsonShmoys.planarDrawingOn_of_edgeSet_subset__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T13:16:10.145781+00:00
-- url     : https://prove2.me/theorems/cbcdfa4e-c050-46e9-8b5a-f0736d7522b4
-- title:
--   Restrict a planar drawing to a spanning subgraph
-- statement:
--   This reuses the supplied `HasPlanarDrawingOn` definition and removes the drawing-restriction obligation from the parent. Unpack T's vertex placement and arc assignment, and use those same functions for L. Each drawing condition for an L edge follows from `hLT`; injectivity of the placement is unchanged, and the edge-crossing condition for L follows because its edges are also T edges. The statement retains the same finite ordered vertex type, so the drawing's endpoints and ordering conventions are preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_of_edgeSet_subset__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {L T : SimpleGraph V}
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hLT : L.edgeSet ⊆ T.edgeSet) :
    WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
