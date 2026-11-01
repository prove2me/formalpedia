-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph__p2m_3121b121_e79f_417e_a8b9_78e91a636a8c_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_3121b121_e79f_417e_a8b9_78e91a636a8c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:43.528102+00:00
-- url     : https://prove2.me/theorems/19c64167-1c0e-4c4b-ad8b-9aac5144fe63
-- title:
--   Drawable graph extends to a maximal planar graph
-- statement:
--   Any drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph, on the same vertex type, of a drawable simple graph with exactly 3|V|−6 edges. The hypothesis preserves the threshold needed for the triangulation edge count; the conclusion is suitable for applying the parent's maximality condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_3121b121_e79f_417e_a8b9_78e91a636a8c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      HasPlanarDrawingOn T ∧
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel T.Adj := dT
       G.edgeFinset ⊆ T.edgeFinset) ∧
      (letI : DecidableRel T.Adj := dT
       T.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
