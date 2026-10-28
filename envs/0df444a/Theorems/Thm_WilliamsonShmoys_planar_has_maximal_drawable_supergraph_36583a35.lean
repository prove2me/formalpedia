-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_has_maximal_drawable_supergraph_36583a35
-- name    : WilliamsonShmoys.planar_has_maximal_drawable_supergraph_36583a35
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:13:13.816422+00:00
-- url     : https://prove2.me/theorems/5544beb8-ded5-49bb-8dbb-069080612d59
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph maximal among drawable supergraphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_has_maximal_drawable_supergraph_36583a35
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by sorry
