-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph_v4
-- name    : WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph_v4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:48:27.551338+00:00
-- url     : https://prove2.me/theorems/e9504646-630c-4c3b-8776-1242aae467f5
-- title:
--   A drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has an inclusion-maximal drawable supergraph on the same vertex type. The claim removes the finite maximization step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P ≤ N := by sorry
