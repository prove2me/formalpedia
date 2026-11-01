-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
-- name    : WilliamsonShmoys.maximal_planar_drawing_connected__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:04.807792+00:00
-- url     : https://prove2.me/theorems/eac4b9bf-b9de-453f-87dd-f5b281d0717e
-- title:
--   Maximal planar supergraphs are connected
-- statement:
--   A planar graph on at least three vertices that is maximal under planar edge extension on the same vertex type is connected. The proof must show that disconnected components can be arranged or redrawn to permit an added edge, rather than presuming an arbitrary arc avoids the existing drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_connected__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.Connected := by sorry
