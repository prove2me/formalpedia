-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:39:44.412083+00:00
-- url     : https://prove2.me/theorems/7356485c-9d8a-4f09-9416-5a0fe1d9ab80
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) : ∃ P : SimpleGraph V, G ≤ P ∧ HasPlanarDrawingOn P ∧ ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P := by sorry
