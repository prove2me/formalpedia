-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_connected__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:06:52.420996+00:00
-- url     : https://prove2.me/theorems/bb4fff64-74f4-4b90-94e5-c66daa170ebe
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict edge-set extension is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_connected__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    M.Connected := by sorry
