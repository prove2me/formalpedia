-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:29:45.106546+00:00
-- url     : https://prove2.me/theorems/346cbd2e-54dd-4cc1-8c07-090cbf4f0cd3
-- title:
--   Euler and face-count data from a planar drawing
-- statement:
--   For a connected simple graph with at least three vertices, a drawing satisfying HasPlanarDrawingOn yields a face count f such that Euler’s formula holds and the sum of face-boundary lengths gives 3f ≤ 2m. The size condition excludes the single-edge embedding, whose sole face boundary has length two. A proof route is to view the finitely many injective arcs as an embedding of the graph in the sphere, use connectedness to obtain disk faces and Euler’s formula, then count edge sides and use simplicity and the vertex bound to rule out face boundaries of length one or two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hConnected : M.Connected) (hM : HasPlanarDrawingOn M) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * M.edgeSet.ncard := by sorry
