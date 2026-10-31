-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:23:21.282965+00:00
-- url     : https://prove2.me/theorems/679f190b-e95f-4794-847a-2466e4e72023
-- title:
--   Face data from a crossing-free drawing
-- statement:
--   A continuous crossing-free drawing of a connected simple graph with at least three vertices yields finitely many faces whose boundary lengths sum to twice the number of edges, are each at least three, and satisfy Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ (F : Type) (_ : Fintype F) (length : F → ℕ), (∑ f : F, length f) = 2 * G.edgeSet.ncard ∧ (∀ f : F, 3 ≤ length f) ∧ Fintype.card V + Fintype.card F = G.edgeSet.ncard + 2 := by sorry
