-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_730ed87f_4857_4202_bf37_5fbad1be2596
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_730ed87f_4857_4202_bf37_5fbad1be2596
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:56:21.311051+00:00
-- url     : https://prove2.me/theorems/f4710fa6-ea6e-4055-bf7d-b2f392aa08bc
-- title:
--   A maximal planar drawing has exactly 3n−6 edges
-- statement:
--   A drawable simple graph on at least three finite ordered vertices with no strictly larger drawable supergraph on those vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_730ed87f_4857_4202_bf37_5fbad1be2596 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
