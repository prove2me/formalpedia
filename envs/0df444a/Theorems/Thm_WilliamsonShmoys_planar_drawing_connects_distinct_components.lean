-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connects_distinct_components
-- name    : WilliamsonShmoys.planar_drawing_connects_distinct_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:41:49.817165+00:00
-- url     : https://prove2.me/theorems/1676ed9e-6226-4dc5-9f39-dd497a5ebd97
-- title:
--   Draw an edge between fixed distinct components
-- statement:
--   For a graph with a crossing-free drawing, any two distinct vertices in different components can be joined by adding their edge while retaining a crossing-free drawing. This removes the topological work from the parent theorem. A proof route is to redraw the components with the selected vertices incident to a common unbounded face, arrange the components disjointly, and draw the added edge through that face. The distinctness and nonreachability hypotheses ensure the added edge joins separate components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connects_distinct_components
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    {u v : V}
    (huv : u ≠ v)
    (hseparate : ¬ P.Reachable u v) :
    WilliamsonShmoys.HasPlanarDrawingOn
      (P ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  sorry
