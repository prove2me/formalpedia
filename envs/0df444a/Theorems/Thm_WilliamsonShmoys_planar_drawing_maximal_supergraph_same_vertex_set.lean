-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_same_vertex_set
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_same_vertex_set
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:24:01.684984+00:00
-- url     : https://prove2.me/theorems/3f07727a-9eae-49ac-be43-9686ad605d53
-- title:
--   Maximal planar supergraph on the same vertex set
-- statement:
--   On the same finite vertex type, extend a graph admitting a planar drawing to one that admits a planar drawing, contains all its edges, and has no drawing-admitting strict supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_same_vertex_set
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun H : SimpleGraph V =>
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      L.edgeSet ⊆ H.edgeSet /\
      ∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K →
        H.edgeSet ⊂ K.edgeSet → False := by sorry
