-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:33:41.184256+00:00
-- url     : https://prove2.me/theorems/a84ead85-80cb-4af4-8df8-cd68693af2dc
-- title:
--   A maximal drawable graph meets the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : forall Y : SimpleGraph V,
      LE.le X Y -> WilliamsonShmoys.HasPlanarDrawingOn Y -> Y = X)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= X.edgeSet.ncard := by sorry
