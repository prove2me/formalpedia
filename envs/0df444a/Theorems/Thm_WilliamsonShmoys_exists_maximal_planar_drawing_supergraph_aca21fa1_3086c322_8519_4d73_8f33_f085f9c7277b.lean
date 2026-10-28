-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:07:24.852973+00:00
-- url     : https://prove2.me/theorems/a0a6c575-1208-4580-bd2f-8d2b4d790de5
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      HasPlanarDrawingOn W ∧
      (∀ u v, Z.Adj u v → W.Adj u v) ∧
      (∀ X : SimpleGraph V, HasPlanarDrawingOn X →
        (∀ u v, W.Adj u v → X.Adj u v) → X = W) := by sorry
