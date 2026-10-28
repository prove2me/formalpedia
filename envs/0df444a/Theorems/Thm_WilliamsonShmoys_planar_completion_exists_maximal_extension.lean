-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_exists_maximal_extension
-- name    : WilliamsonShmoys.planar_completion_exists_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:19:55.88119+00:00
-- url     : https://prove2.me/theorems/7c4503f5-896e-4e8c-af2a-08bda28bfad9
-- title:
--   A maximal drawable extension exists
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_exists_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hdraw : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
