-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:30:17.430334+00:00
-- url     : https://prove2.me/theorems/873dde20-79e9-4f77-962d-78285a200769
-- title:
--   Lower edge bound for a maximal finite planar graph
-- statement:
--   A drawable finite simple graph on at least three vertices that has no drawable proper supergraph on the same vertex set has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T) (hMax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by sorry
