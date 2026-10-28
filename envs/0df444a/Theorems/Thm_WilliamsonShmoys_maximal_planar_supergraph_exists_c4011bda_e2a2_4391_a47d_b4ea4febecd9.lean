-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:42:11.779829+00:00
-- url     : https://prove2.me/theorems/f0db8943-9305-4363-9208-b45f79310e3a
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has an inclusion-maximal drawable supergraph on that same type. This supplies the maximal extension used by the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_exists_c4011bda_e2a2_4391_a47d_b4ea4febecd9
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N := by sorry
