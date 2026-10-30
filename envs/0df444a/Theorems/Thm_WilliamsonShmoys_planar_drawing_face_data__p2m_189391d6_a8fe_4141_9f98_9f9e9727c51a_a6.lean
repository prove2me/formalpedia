-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_189391d6_a8fe_4141_9f98_9f9e9727c51a_a6
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_189391d6_a8fe_4141_9f98_9f9e9727c51a_a6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:47:56.233799+00:00
-- url     : https://prove2.me/theorems/419a2436-4d06-4690-848e-d5938efdd81b
-- title:
--   A connected drawn graph admits finite face data
-- statement:
--   Construct finite face data for the graph's drawing: every face has at least three directed edges, contains only graph darts, and each graph dart belongs to exactly one face; the vertex, face, and edge counts satisfy Euler's formula. This isolates the topological embedding and face-construction argument from the parent. A proof route is to form facial boundary walks from the drawing's local cyclic orders and prove the connected plane graph Euler formula. Establishing that construction from the given continuous arcs remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_189391d6_a8fe_4141_9f98_9f9e9727c51a_a6 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : HasPlanarDrawingOn H) (hCard : 3 <= Fintype.card V) : ∃ faces : Finset (Finset (V × V)), (∀ F ∈ faces, 3 <= F.card) ∧ (∀ F ∈ faces, ∀ d ∈ F, H.Adj d.1 d.2) ∧ (∀ u v, H.Adj u v ↔ ∃! F, F ∈ faces ∧ (u, v) ∈ F) ∧ Fintype.card V + faces.card = H.edgeSet.ncard + 2 := by sorry
