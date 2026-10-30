-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:22:41.430753+00:00
-- url     : https://prove2.me/theorems/648e2563-4933-48d5-af68-a43e4e82ab0d
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal finite simple graph with a crossing-free drawing and at least three vertices has exactly 3|V|−6 edges. Maximality makes every face triangular; Euler’s formula and face-edge incidence counting give the equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
