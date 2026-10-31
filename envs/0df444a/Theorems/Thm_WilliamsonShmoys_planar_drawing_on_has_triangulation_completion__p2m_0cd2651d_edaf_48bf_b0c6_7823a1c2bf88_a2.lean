-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_has_triangulation_completion__p2m_0cd2651d_edaf_48bf_b0c6_7823a1c2bf88_a2
-- name    : WilliamsonShmoys.planar_drawing_on_has_triangulation_completion__p2m_0cd2651d_edaf_48bf_b0c6_7823a1c2bf88_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:04.142993+00:00
-- url     : https://prove2.me/theorems/a983af35-26d8-44a9-8810-a80e355bc9cf
-- title:
--   Every drawable graph has a triangulated drawable completion
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_has_triangulation_completion__p2m_0cd2651d_edaf_48bf_b0c6_7823a1c2bf88_a2 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 <= Fintype.card V) (hT : HasPlanarDrawingOn T) : Exists fun U : SimpleGraph V => T <= U ∧ HasPlanarDrawingOn U ∧ 3 * Fintype.card V - 6 = U.edgeSet.ncard := by
  sorry
