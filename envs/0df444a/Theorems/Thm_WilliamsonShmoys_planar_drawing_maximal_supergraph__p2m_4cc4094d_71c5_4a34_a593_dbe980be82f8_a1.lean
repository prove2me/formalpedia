-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:08.262424+00:00
-- url     : https://prove2.me/theorems/e1d0a0ee-343a-44fb-acd2-3b165723c48a
-- title:
--   A planar drawing has a maximal planar supergraph
-- statement:
--   Every finite planar graph on a fixed vertex type is contained in a planar supergraph maximal under inclusion. Prove this by selecting a planar supergraph containing J with the largest edge-set cardinality; any planar supergraph of the selected graph must then have the same edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
