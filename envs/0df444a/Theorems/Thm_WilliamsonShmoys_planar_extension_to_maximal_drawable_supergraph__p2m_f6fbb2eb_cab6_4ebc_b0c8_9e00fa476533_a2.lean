-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_to_maximal_drawable_supergraph__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2
-- name    : WilliamsonShmoys.planar_extension_to_maximal_drawable_supergraph__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:23:53.42858+00:00
-- url     : https://prove2.me/theorems/0dcbb486-686a-4b67-b195-425afb057726
-- title:
--   Extension to an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_to_maximal_drawable_supergraph__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) := by sorry
