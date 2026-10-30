-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:28:32.868212+00:00
-- url     : https://prove2.me/theorems/45047076-5ab9-4c90-a376-79779925d62b
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite connected drawable graph on at least three vertices has an inclusion-maximal drawable supergraph on the same vertex type, which remains connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
    {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hU : HasPlanarDrawingOn U)
    (hconn : U.Connected) :
    ∃ T : SimpleGraph V, U ≤ T ∧ HasPlanarDrawingOn T ∧ T.Connected ∧
      ∀ S : SimpleGraph V, T ≤ S → HasPlanarDrawingOn S → S = T := by sorry
