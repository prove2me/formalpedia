-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_faceCounts__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2
-- name    : WilliamsonShmoys.planarDrawingOn_faceCounts__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:16.600979+00:00
-- url     : https://prove2.me/theorems/012f04df-75c0-41fb-9a08-dc6665997d71
-- title:
--   Extract face counts from a planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there are finitely many face lengths satisfying Euler’s equation, the edge-side incidence count, and a lower bound of three for each face. The size condition is retained to exclude degenerate face boundaries. This removes the topological construction and counting work from the parent. A proof route is to obtain cyclic orders and face walks from the drawing, prove Euler’s formula for the resulting plane embedding, and count the two sides of each edge. The remaining core obligation is that topological formalization.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_faceCounts__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConnected : H.Connected) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ (F : ℕ) (faceLength : Fin F → ℕ), ((Fintype.card V : ℤ) - (H.edgeSet.ncard : ℤ) + (F : ℤ) = 2) ∧ (∑ f : Fin F, faceLength f) = 2 * H.edgeSet.ncard ∧ ∀ f, 3 ≤ faceLength f := by sorry
