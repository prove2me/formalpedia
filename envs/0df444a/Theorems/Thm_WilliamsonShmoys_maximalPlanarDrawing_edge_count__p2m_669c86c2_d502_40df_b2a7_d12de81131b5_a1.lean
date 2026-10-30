-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawing_edge_count__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1
-- name    : WilliamsonShmoys.maximalPlanarDrawing_edge_count__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:46:59.068784+00:00
-- url     : https://prove2.me/theorems/a7addf37-64f9-4244-8efd-795054181733
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A planar graph on at least three vertices that has no strictly larger planar supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximalPlanarDrawing_edge_count__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hV : LE.le 3 (Fintype.card V)) (hmax : ∀ N : SimpleGraph V, LE.le M N → HasPlanarDrawingOn N → N = M) : 3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
