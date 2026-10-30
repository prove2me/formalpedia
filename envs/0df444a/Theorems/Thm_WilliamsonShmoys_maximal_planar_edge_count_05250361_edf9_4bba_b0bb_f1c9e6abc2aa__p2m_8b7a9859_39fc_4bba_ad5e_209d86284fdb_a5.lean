-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
-- name    : WilliamsonShmoys.maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T01:42:16.153773+00:00
-- url     : https://prove2.me/theorems/7b588b35-5745-43b6-a4fa-de8b7ff612dc
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable edge extension has exactly 3|V|−6 edges. The proof route is to obtain a planar embedding, handle connectivity forced by maximality, show every face is triangular, and apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V,
      (∀ {u v : V}, Q.Adj u v → R.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    (Q.edgeSet.ncard : Int) =
      (3 : Int) * (Fintype.card V : Int) - 6 := by sorry
