-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T01:00:43.889239+00:00
-- url     : https://prove2.me/theorems/d46620b3-b697-4ad1-8012-dcd7eecf2863
-- title:
--   A planar graph has a maximal planar supergraph on the same vertices
-- statement:
--   Every planar graph on a finite vertex type has a planar supergraph on that same type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ G : SimpleGraph V, H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H := by sorry
