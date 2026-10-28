-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:08:14.961914+00:00
-- url     : https://prove2.me/theorems/df2c1521-453b-41e8-a2f2-30b899461f2c
-- title:
--   Every drawable graph has an edge-maximal drawable extension
-- statement:
--   Every finite drawable graph is contained in a drawable graph on the same vertex type that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ P := by sorry
