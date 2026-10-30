-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:27:41.625155+00:00
-- url     : https://prove2.me/theorems/8b7a9859-39fc-4bba-ad5e-209d86284fdb
-- title:
--   Triangulation extension of a planar drawing
-- statement:
--   For a finite simple graph with at least three vertices and the specified planar drawing, there is a planar simple supergraph on the same vertex type that contains every original edge and has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ Q : SimpleGraph V,
      (∀ {u v : V}, M.Adj u v → Q.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (M.edgeSet.ncard : Int) ≤ (Q.edgeSet.ncard : Int) ∧
      (Q.edgeSet.ncard : Int) =
        (3 : Int) * (Fintype.card V : Int) - 6 := by sorry
