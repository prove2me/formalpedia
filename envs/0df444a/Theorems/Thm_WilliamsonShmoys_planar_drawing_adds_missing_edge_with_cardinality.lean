-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_adds_missing_edge_with_cardinality
-- name    : WilliamsonShmoys.planar_drawing_adds_missing_edge_with_cardinality
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:34:44.185735+00:00
-- url     : https://prove2.me/theorems/3a656764-22f2-4932-92d5-5463247600c7
-- title:
--   Add a missing edge to a disconnected planar drawing
-- statement:
--   A disconnected graph on a finite linearly ordered vertex type of cardinality at least three, with a drawing satisfying the specified crossing-free arc conditions, can be augmented by one edge between distinct nonadjacent vertices while retaining such a drawing. The cardinality bound rules out the empty-type counterexample to the earlier unrestricted augmentation statement. A proof can proceed through complementary-face incidence among the finitely many embedded components and an arc drawn through a shared face. This is the remaining geometric obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_adds_missing_edge_with_cardinality
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hDisconnected : ¬ P.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ P.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn
        (P ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  sorry
