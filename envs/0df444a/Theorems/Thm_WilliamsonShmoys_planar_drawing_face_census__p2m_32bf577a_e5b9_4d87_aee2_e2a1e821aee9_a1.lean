-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_census__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1
-- name    : WilliamsonShmoys.planar_drawing_face_census__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:31.230939+00:00
-- url     : https://prove2.me/theorems/166f58f8-d1da-4fce-9ab9-52a0e477460a
-- title:
--   Face census for a connected planar drawing
-- statement:
--   A connected graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a finite collection of face boundary lengths. Their count satisfies Euler’s equation; their total length counts each edge twice; and every boundary length is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open scoped BigOperators

theorem WilliamsonShmoys.planar_drawing_face_census__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hcard : 3 <= Fintype.card V) : ∃ (F : ℕ) (boundary : Fin F → ℕ), Fintype.card V + F = K.edgeFinset.card + 2 ∧ (∑ f : Fin F, boundary f) = 2 * K.edgeFinset.card ∧ ∀ f : Fin F, 3 <= boundary f := by sorry
