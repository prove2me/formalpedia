-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_edge_count_lower__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
-- name    : WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_lower__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:00:31.437002+00:00
-- url     : https://prove2.me/theorems/77e6a9aa-019b-4811-bd18-07d7e3258778
-- title:
--   Maximal planar drawing edge-count lower bound
-- statement:
--   A drawable graph on at least three finite vertices that is maximal among drawable supergraphs on the same vertex type has at least three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_lower__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
