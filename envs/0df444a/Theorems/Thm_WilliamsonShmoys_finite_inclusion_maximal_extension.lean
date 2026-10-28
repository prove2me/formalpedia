-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_inclusion_maximal_extension
-- name    : WilliamsonShmoys.finite_inclusion_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:15:55.23907+00:00
-- url     : https://prove2.me/theorems/af59b4ee-808d-45a7-aa0d-f0b6fcbb8506
-- title:
--   A drawable graph has a finite inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under inclusion among drawable supergraphs. Choose a supergraph with the greatest edge count from the finite nonempty family; inclusion and equal edge counts imply equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_inclusion_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hWdraw : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ T : SimpleGraph V,
      W ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V,
        T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T := by sorry
