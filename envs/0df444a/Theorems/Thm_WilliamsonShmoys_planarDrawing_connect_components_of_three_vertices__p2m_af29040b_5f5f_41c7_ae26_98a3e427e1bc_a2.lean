-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_connect_components_of_three_vertices__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a2
-- name    : WilliamsonShmoys.planarDrawing_connect_components_of_three_vertices__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:37.113259+00:00
-- url     : https://prove2.me/theorems/166f36ec-46e1-45a5-b168-5ae07e468a01
-- title:
--   Connect components of a finite planar drawing with at least three vertices
-- statement:
--   A finite planar drawing on at least three vertices can be extended to a connected planar graph on the same vertex set, retaining every original edge and therefore not decreasing the edge count. The vertex bound ensures nonemptiness, avoiding the empty-type counterexample to the earlier child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_connect_components_of_three_vertices__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
        (letI : DecidableRel G.Adj := dG
         letI : DecidableRel H.Adj := dH
         G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
