-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
-- name    : WilliamsonShmoys.maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:00:55.687393+00:00
-- url     : https://prove2.me/theorems/2073dc9f-e309-4751-b73f-44a33c99a7cb
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A graph with the specified planar drawing that has no strictly larger drawable supergraph on the same vertices has exactly 3|V|−6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V,
      (∀ {u v : V}, Q.Adj u v → R.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    (Q.edgeSet.ncard : Int) =
      (3 : Int) * (Fintype.card V : Int) - 6 := by sorry
