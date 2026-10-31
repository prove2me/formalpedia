-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation__p2m_ff509257_2aef_46e4_8d24_c01568aee116_a1
-- name    : WilliamsonShmoys.maximal_planar_triangulation__p2m_ff509257_2aef_46e4_8d24_c01568aee116_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:53:49.937025+00:00
-- url     : https://prove2.me/theorems/2bf11b69-7074-453d-b4a4-93e188db5490
-- title:
--   Extend a finite planar drawing to a triangulation
-- statement:
--   For a finite vertex type with at least three vertices, any graph admitting the specified planar drawing is a subgraph of a planar graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_triangulation__p2m_ff509257_2aef_46e4_8d24_c01568aee116_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : ∃ T : SimpleGraph V, HasPlanarDrawingOn T ∧ H ≤ T ∧ T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
