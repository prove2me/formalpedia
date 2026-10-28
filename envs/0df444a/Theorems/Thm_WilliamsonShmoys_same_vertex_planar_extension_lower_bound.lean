-- Prove2me | Theorems.Thm_WilliamsonShmoys_same_vertex_planar_extension_lower_bound
-- name    : WilliamsonShmoys.same_vertex_planar_extension_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:24:02.597149+00:00
-- url     : https://prove2.me/theorems/461941b6-8dbe-4844-a709-3e81d4ca08ca
-- title:
--   Planar extension with the triangulation edge lower bound
-- statement:
--   Every planar graph on a fixed finite vertex type of size at least three has a planar supergraph on that same type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.same_vertex_planar_extension_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    exists K : SimpleGraph V,
      G <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      3 * Fintype.card V - 6 <= K.edgeSet.ncard := by sorry
