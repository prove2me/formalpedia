-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_strict_supergraph_of_three_vertices
-- name    : WilliamsonShmoys.planar_disconnected_has_strict_supergraph_of_three_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:33:10.73298+00:00
-- url     : https://prove2.me/theorems/866790dd-01b0-424d-966e-6ad13ddfaff0
-- title:
--   A disconnected planar graph on at least three vertices has a strict planar extension
-- statement:
--   A disconnected graph on at least three vertices with the specified crossing-free drawing can be extended by an edge to a strict supergraph with such a drawing. The cardinality hypothesis rules out the empty-type counterexample to the earlier unrestricted child. A proof can join two components through a face of the drawing; formalizing that topological construction is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_has_strict_supergraph_of_three_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
