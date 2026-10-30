-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:49:46.43748+00:00
-- url     : https://prove2.me/theorems/35a18409-012a-454b-b7d9-810131c10ca7
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
