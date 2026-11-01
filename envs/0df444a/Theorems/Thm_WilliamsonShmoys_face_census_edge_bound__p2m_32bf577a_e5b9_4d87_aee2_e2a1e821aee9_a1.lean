-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_census_edge_bound__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1
-- name    : WilliamsonShmoys.face_census_edge_bound__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:33.704434+00:00
-- url     : https://prove2.me/theorems/f30317bd-17c2-4697-b584-56453e630be8
-- title:
--   Edge bound from a face census
-- statement:
--   For a finite graph, if a face census satisfies Euler’s equation, counts every edge twice in total boundary length, and gives each face boundary length at least three, then the graph has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open scoped BigOperators

theorem WilliamsonShmoys.face_census_edge_bound__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (F : ℕ) (boundary : Fin F → ℕ) (hEuler : Fintype.card V + F = K.edgeFinset.card + 2) (hDouble : (∑ f : Fin F, boundary f) = 2 * K.edgeFinset.card) (hFaces : ∀ f : Fin F, 3 <= boundary f) : K.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
