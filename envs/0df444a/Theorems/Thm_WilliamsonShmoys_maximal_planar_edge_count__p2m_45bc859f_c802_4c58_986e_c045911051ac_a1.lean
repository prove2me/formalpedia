-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:04.961151+00:00
-- url     : https://prove2.me/theorems/4536f73e-ef32-44ed-9a4a-358d0b7012c5
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex set has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) (hCard : 3 ≤ Fintype.card V) : J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
