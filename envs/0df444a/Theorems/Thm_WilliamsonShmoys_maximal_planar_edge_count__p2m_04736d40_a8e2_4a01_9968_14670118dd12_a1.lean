-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:55:15.305606+00:00
-- url     : https://prove2.me/theorems/f9dc181e-d230-4644-be1b-965b4f83a602
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An edge-maximal graph with a planar drawing and at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
