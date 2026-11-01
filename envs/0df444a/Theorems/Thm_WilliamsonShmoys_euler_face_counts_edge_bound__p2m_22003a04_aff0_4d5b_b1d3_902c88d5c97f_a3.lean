-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_counts_edge_bound__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a3
-- name    : WilliamsonShmoys.euler_face_counts_edge_bound__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:30:43.025234+00:00
-- url     : https://prove2.me/theorems/52bfcd75-96b2-4acf-a3c5-54d7a7e7a41b
-- title:
--   Derive the planar edge bound from Euler counts
-- statement:
--   Derive the target edge inequality from an exact edge count, Euler’s equation, and the face-incidence bound. Multiplying Euler’s equation by three and combining it with the face inequality gives the result by natural-number linear arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.euler_face_counts_edge_bound__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (edgeCount faceCount : ℕ)
    (hEdges : G.edgeSet.ncard = edgeCount)
    (hEuler : Fintype.card V + faceCount = edgeCount + 2)
    (hFaces : 3 * faceCount <= 2 * edgeCount) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
