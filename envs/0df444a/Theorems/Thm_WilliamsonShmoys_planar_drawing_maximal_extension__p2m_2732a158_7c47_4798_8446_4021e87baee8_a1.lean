-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_2732a158_7c47_4798_8446_4021e87baee8_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2732a158_7c47_4798_8446_4021e87baee8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:40:02.065733+00:00
-- url     : https://prove2.me/theorems/bed1e8e9-9063-4971-87d4-a573a94b3117
-- title:
--   Maximal planar extension on the same vertex set
-- statement:
--   Every finite graph with at least three vertices that admits the specified planar drawing has a drawing-admitting supergraph on the same vertex type that contains all its edges and is inclusion-maximal among drawing-admitting supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2732a158_7c47_4798_8446_4021e87baee8_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 <= Fintype.card V) (hHplanar : HasPlanarDrawingOn H) : ∃ T : SimpleGraph V, H ≤ T ∧ H.edgeSet ⊆ T.edgeSet ∧ HasPlanarDrawingOn T ∧ (∀ S : SimpleGraph V, T ≤ S → HasPlanarDrawingOn S → S = T) := by sorry
