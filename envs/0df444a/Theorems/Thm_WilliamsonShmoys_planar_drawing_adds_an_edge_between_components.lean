-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_adds_an_edge_between_components
-- name    : WilliamsonShmoys.planar_drawing_adds_an_edge_between_components
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T09:22:44.133875+00:00
-- url     : https://prove2.me/theorems/568d8080-eaf2-4c6b-8a41-f2ec7a8c6508
-- title:
--   Add an edge between components of a planar drawing
-- statement:
--   A finite disconnected graph with a drawing satisfying the specified crossing-free arc conditions admits a new edge between distinct nonadjacent vertices while preserving those drawing conditions. The vertices can be chosen in distinct components incident to a common complementary face; an arc through that face joins them without introducing intersections with the existing drawing. The remaining proof requires formalizing the finite plane-embedding and face-incidence argument, including nested components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_adds_an_edge_between_components
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hDisconnected : ¬ P.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ P.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn
        (P ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  sorry
