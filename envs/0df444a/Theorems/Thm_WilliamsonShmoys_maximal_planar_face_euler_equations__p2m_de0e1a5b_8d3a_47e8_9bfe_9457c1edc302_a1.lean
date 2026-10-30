-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_euler_equations__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
-- name    : WilliamsonShmoys.maximal_planar_face_euler_equations__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T07:02:41.788001+00:00
-- url     : https://prove2.me/theorems/4f918f75-55a8-4d80-8ca8-662e2486c7e0
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a maximal drawable simple graph on at least three vertices, produce a natural number of faces satisfying Euler’s vertex-face-edge equation and the triangular-face incidence equation. The independent proof route is to derive a finite plane embedding from the drawing witnesses, apply Euler’s formula, and show maximality forces every face boundary to be triangular: a boundary permitting a diagonal would contradict maximality. This removes the topological face counting from the parent. The three-vertex boundary case is included; the parent still needs the extension child and the short arithmetic combination.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_euler_equations__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (M : SimpleGraph C.supp)
    [Fintype C.supp]
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph C.supp, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ C.supp.ncard) :
    ∃ f : ℕ,
      C.supp.ncard + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by sorry
