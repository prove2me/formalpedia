-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:28.76252+00:00
-- url     : https://prove2.me/theorems/543fa1c4-4e11-411c-bac5-e006f931bb82
-- title:
--   Maximal planar drawing edge count lower bound
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has at least 3|V|−6 edges. Maximality rules out faces that could be triangulated by adding an edge; the remaining work is to formalize that augmentation and count incidences using Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hMax : ∀ H' : SimpleGraph V, H ≤ H' → H' ≠ H → ¬ WilliamsonShmoys.HasPlanarDrawingOn H') (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
