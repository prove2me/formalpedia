-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:45.130982+00:00
-- url     : https://prove2.me/theorems/35c6358d-b566-416e-bb3d-7356a75007d9
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal simple planar graph on a finite vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
