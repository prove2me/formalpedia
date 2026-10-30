-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_b3857576_7612_4991_8128_4575dd8808dc_a1
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_b3857576_7612_4991_8128_4575dd8808dc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:19:56.071866+00:00
-- url     : https://prove2.me/theorems/5ed93e11-5366-47c6-a614-dcb01ec690c9
-- title:
--   Euler and face-incidence equations for a maximal drawable graph
-- statement:
--   For a finite drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set, there is a face count f satisfying Euler’s equation and the triangular face-edge incidence equation. These equations imply the target edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_b3857576_7612_4991_8128_4575dd8808dc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by sorry
