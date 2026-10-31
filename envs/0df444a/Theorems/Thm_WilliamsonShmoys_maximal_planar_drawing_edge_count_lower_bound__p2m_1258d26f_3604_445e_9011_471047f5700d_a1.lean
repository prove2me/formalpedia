-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:24.84765+00:00
-- url     : https://prove2.me/theorems/c7182b6b-7db6-44e9-8732-a23951984627
-- title:
--   Maximal drawing forces the triangulation lower bound
-- statement:
--   For a drawable finite simple graph with at least three vertices, if every drawable supergraph on the same vertex type is already a subgraph of it, then it has at least `3|V| - 6` edges. The proof route is to show maximality rules out faces with more than three boundary sides, then apply Euler’s formula and count edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
