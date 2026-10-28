-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_repair3
-- name    : WilliamsonShmoys.planar_supergraph_exists_repair3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:35:07.647588+00:00
-- url     : https://prove2.me/theorems/6ed2b6bf-60ad-433f-b070-ca0d6b4cc479
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Among all drawable simple graphs on the fixed finite vertex type that contain `G`, choose one with the largest number of edges. It has no drawable strict supergraph. There is no small-vertex exception needed for this finite maximization argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_exists_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V,
      HasPlanarDrawingOn T ∧
      (∀ u v, G.Adj u v → T.Adj u v) ∧
      ∀ U : SimpleGraph V,
        HasPlanarDrawingOn U →
        (∀ u v, T.Adj u v → U.Adj u v) →
        (∀ u v, U.Adj u v → T.Adj u v) := by sorry
