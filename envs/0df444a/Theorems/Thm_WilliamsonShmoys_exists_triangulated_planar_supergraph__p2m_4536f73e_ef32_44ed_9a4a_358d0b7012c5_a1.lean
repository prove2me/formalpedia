-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph__p2m_4536f73e_ef32_44ed_9a4a_358d0b7012c5_a1
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_4536f73e_ef32_44ed_9a4a_358d0b7012c5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:39.226324+00:00
-- url     : https://prove2.me/theorems/5045813e-840e-441f-8744-eff11fe55168
-- title:
--   Every drawable finite graph extends to a triangulated drawable supergraph
-- statement:
--   Any finite drawable simple graph on at least three vertices is a spanning subgraph of a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_4536f73e_ef32_44ed_9a4a_358d0b7012c5_a1 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) (hCard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
