-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_completion_953852c9
-- name    : WilliamsonShmoys.planar_drawing_euler_completion_953852c9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:29:36.07287+00:00
-- url     : https://prove2.me/theorems/f95845a8-fe71-4221-9cf1-00b67c57c4ac
-- title:
--   Euler-count completion of a drawable graph
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices whose edge count satisfies Euler's maximal-planar equality. The child isolates the drawing extension and planar face-counting argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_completion_953852c9
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
