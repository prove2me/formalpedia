-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on_same_vertex_type__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertex_type__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:54:24.158842+00:00
-- url     : https://prove2.me/theorems/5269810a-aaa3-482e-ac1c-32cbc68ffb91
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every finite graph with at least three vertices and a drawing of the specified kind is contained in a graph on the same vertex type that is maximal among its planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertex_type__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by sorry
