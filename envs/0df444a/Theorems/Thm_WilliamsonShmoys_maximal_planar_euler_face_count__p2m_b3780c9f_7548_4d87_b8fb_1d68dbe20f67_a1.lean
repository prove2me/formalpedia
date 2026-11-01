-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_count__p2m_b3780c9f_7548_4d87_b8fb_1d68dbe20f67_a1
-- name    : WilliamsonShmoys.maximal_planar_euler_face_count__p2m_b3780c9f_7548_4d87_b8fb_1d68dbe20f67_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:39.014494+00:00
-- url     : https://prove2.me/theorems/af125c13-d52b-4d2e-8606-f76458469e69
-- title:
--   Euler and triangular-face counts for maximal planar drawings
-- statement:
--   For a maximal planar drawing on at least three vertices, there is a finite face count f such that Euler’s relation holds and the total number of face sides is three per face and two per edge. Prove this by passing from the arc drawing to a finite plane embedding, showing maximality makes the graph connected with triangular faces, then applying Euler’s formula and counting edge-side incidences. The boundary case of the three-vertex triangle has two faces and satisfies both equations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_euler_face_count__p2m_b3780c9f_7548_4d87_b8fb_1d68dbe20f67_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by
  sorry
