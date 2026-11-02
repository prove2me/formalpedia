-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_drawable_supergraph__p2m_afa4574a_1607_44bb_93bd_58940dcb1487_a2
-- name    : WilliamsonShmoys.exists_triangulated_drawable_supergraph__p2m_afa4574a_1607_44bb_93bd_58940dcb1487_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:48:43.179654+00:00
-- url     : https://prove2.me/theorems/f0debea5-402c-48d1-9751-ec911f78abab
-- title:
--   A drawable graph extends to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices extends, on the same vertex set, to a drawable graph whose edge count is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulated_drawable_supergraph__p2m_afa4574a_1607_44bb_93bd_58940dcb1487_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hcard : 3 ≤ Fintype.card V) (hM : HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, ∃ (hNdec : DecidableRel N.Adj), M ≤ N ∧ HasPlanarDrawingOn N ∧ (letI : DecidableRel N.Adj := hNdec; N.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
