-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension
-- name    : WilliamsonShmoys.exists_maximal_planar_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:32:04.882415+00:00
-- url     : https://prove2.me/theorems/615a7193-046c-4d54-b565-1daa5cd808b6
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable finite simple graph is contained in a drawable graph on the same vertex type that is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
