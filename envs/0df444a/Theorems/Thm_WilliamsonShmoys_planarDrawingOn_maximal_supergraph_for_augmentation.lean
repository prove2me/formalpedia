-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximal_supergraph_for_augmentation
-- name    : WilliamsonShmoys.planarDrawingOn_maximal_supergraph_for_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:41:31.62539+00:00
-- url     : https://prove2.me/theorems/055d5cca-8d6d-4297-8bdb-1b5664225212
-- title:
--   Maximal drawable supergraph for augmentation
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_maximal_supergraph_for_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
