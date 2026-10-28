-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:32:58.563675+00:00
-- url     : https://prove2.me/theorems/4c4f74a2-ec7b-480d-9c93-7d5d7c28fff6
-- title:
--   A drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that has no strictly larger drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_e951fa7c_3e6e_4109_8011_74ed7e6927fa
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V,
      LE.le W X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      (forall Y : SimpleGraph V,
        LE.le X Y -> WilliamsonShmoys.HasPlanarDrawingOn Y -> Y = X) := by sorry
