-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_is_connected__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- name    : WilliamsonShmoys.maximal_drawable_is_connected__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:39:47.562788+00:00
-- url     : https://prove2.me/theorems/9bb32eb0-a144-4276-9cbf-a7f4026975ff
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   A maximal drawable graph with at least three vertices is connected, since separate components can be joined by a noncrossing edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_is_connected__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hP : HasPlanarDrawingOn P) (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P) : P.Connected := by sorry
