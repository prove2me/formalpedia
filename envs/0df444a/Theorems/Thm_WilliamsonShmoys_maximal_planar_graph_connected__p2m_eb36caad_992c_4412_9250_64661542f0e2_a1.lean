-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_connected__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:30:53.167524+00:00
-- url     : https://prove2.me/theorems/008dc069-b8e6-4096-b412-eae96eda23f6
-- title:
--   Maximal planar graphs with at least three vertices are connected
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on a finite vertex type of size at least three is connected. If it were disconnected, a curve in the complement of the drawing would allow an edge between components, contradicting maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_connected__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    K.Connected := by sorry
