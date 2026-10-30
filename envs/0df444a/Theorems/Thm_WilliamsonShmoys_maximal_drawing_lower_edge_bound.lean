-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_lower_edge_bound
-- name    : WilliamsonShmoys.maximal_drawing_lower_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:41:28.054543+00:00
-- url     : https://prove2.me/theorems/679bf6a6-fac0-4eb8-a381-2f80a1e33cc2
-- title:
--   Lower edge bound for maximal drawable graphs
-- statement:
--   A drawable graph that is maximal under adding edges on its fixed vertex set, with at least three vertices, has at least 3n−6 edges. This is the central geometric obligation. A proof route is to show maximality forces every face in the associated plane embedding to be triangular, then apply Euler’s formula and count face-edge incidences. The boundary case n=3 gives the lower bound of three edges; the stated hypotheses exclude smaller vertex sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_lower_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊂ K.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
