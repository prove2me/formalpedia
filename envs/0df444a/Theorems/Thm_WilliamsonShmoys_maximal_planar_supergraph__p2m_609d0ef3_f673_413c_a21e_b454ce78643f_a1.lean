-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_609d0ef3_f673_413c_a21e_b454ce78643f_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_609d0ef3_f673_413c_a21e_b454ce78643f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:04:33.266193+00:00
-- url     : https://prove2.me/theorems/5b41b99b-00ea-48ee-b254-cd4945e2b482
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_609d0ef3_f673_413c_a21e_b454ce78643f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W ≤ X ∧ HasPlanarDrawingOn X ∧
      ∀ Y : SimpleGraph V, X ≤ Y → HasPlanarDrawingOn Y → Y = X := by sorry
