-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_b4255e2c_f98e_48f5_8b5b_17ec5805d9ae_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_b4255e2c_f98e_48f5_8b5b_17ec5805d9ae_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T01:00:37.773212+00:00
-- url     : https://prove2.me/theorems/724a012f-3099-4ee5-9840-4b16b095fdb5
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Any finite drawable graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_b4255e2c_f98e_48f5_8b5b_17ec5805d9ae_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ T : SimpleGraph V, M ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      (∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) := by sorry
