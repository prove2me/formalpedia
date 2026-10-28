-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion_3655d1b6_6c4a_40a3_8c82_ff009c818c61
-- name    : WilliamsonShmoys.exists_maximal_planar_completion_3655d1b6_6c4a_40a3_8c82_ff009c818c61
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:14:30.00569+00:00
-- url     : https://prove2.me/theorems/b87413ec-ee6c-439b-9104-5eab20ee38fe
-- title:
--   Finite maximal drawable supergraph completion
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_completion_3655d1b6_6c4a_40a3_8c82_ff009c818c61 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 <= Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
