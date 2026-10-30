-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_repair3_179e6262
-- name    : WilliamsonShmoys.maximal_planar_edge_count_euler_repair3_179e6262
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:06:28.363442+00:00
-- url     : https://prove2.me/theorems/8fbf46bf-6c81-47ff-a3ad-cd563ec39623
-- title:
--   Edge count of a maximal planar graph from Euler’s formula
-- statement:
--   A drawable simple graph on at least three vertices with no drawable strict supergraph on the same vertex type has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_euler_repair3_179e6262 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) (hCard : 3 ≤ Fintype.card V) : J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
