-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulating_extension__p2m_3c4a1050_73ac_4fb0_b659_1aa33a199ba4_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulating_extension__p2m_3c4a1050_73ac_4fb0_b659_1aa33a199ba4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:01:28.196292+00:00
-- url     : https://prove2.me/theorems/4c570e3e-7abb-4bee-95ce-463a755b298b
-- title:
--   A planar drawing extends to a triangulation
-- statement:
--   Any graph on at least three vertices with a drawing in the specified sense has a drawable supergraph on the same vertices with exactly 3n−6 edges. This is the augmentation-to-triangulation step; the parent uses maximality to identify that supergraph with K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulating_extension__p2m_3c4a1050_73ac_4fb0_b659_1aa33a199ba4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V - 6 = H.edgeFinset.card := by sorry
