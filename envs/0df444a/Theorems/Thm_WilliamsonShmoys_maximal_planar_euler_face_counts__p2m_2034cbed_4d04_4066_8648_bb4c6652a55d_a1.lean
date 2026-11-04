-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_counts__p2m_2034cbed_4d04_4066_8648_bb4c6652a55d_a1
-- name    : WilliamsonShmoys.maximal_planar_euler_face_counts__p2m_2034cbed_4d04_4066_8648_bb4c6652a55d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:41:25.771667+00:00
-- url     : https://prove2.me/theorems/ead8e70c-0f57-40e4-8a7a-12724552c1e7
-- title:
--   Euler and triangular-face counts for a maximal drawable graph
-- statement:
--   For a maximal drawable simple graph on at least three vertices, there is a number of faces satisfying both the spherical Euler equation and the triangular-face incidence equation. At three vertices these equations give the triangular embedding; the size hypothesis also keeps the claimed edge lower bound meaningful under truncated natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_euler_face_counts__p2m_2034cbed_4d04_4066_8648_bb4c6652a55d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    ∃ f : ℕ,
      f + Fintype.card V = N.edgeFinset.card + 2 ∧
      3 * f = 2 * N.edgeFinset.card := by sorry
