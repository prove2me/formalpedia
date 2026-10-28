-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_for_edge_lower_bound
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_supergraph_for_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:12:23.108817+00:00
-- url     : https://prove2.me/theorems/a10529c5-14f2-475e-945f-6b7f9afccfe9
-- title:
--   Maximal planar supergraph for the edge lower bound
-- statement:
--   Every planar drawing on a finite vertex type has a planar supergraph on the same vertices that is maximal under edge inclusion. This new finite-selection lemma removes the existence and maximality step from the parent. Prove it by considering the finite set of planar graphs containing T and choosing one with maximum edge-set cardinality; the candidate set is nonempty because it contains T.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_maximal_supergraph_for_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      (∀ u v, T.Adj u v → U.Adj u v) ∧
      (∀ W : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn W →
        (∀ u v, U.Adj u v → W.Adj u v) →
        ∀ u v, W.Adj u v → U.Adj u v) := by sorry
