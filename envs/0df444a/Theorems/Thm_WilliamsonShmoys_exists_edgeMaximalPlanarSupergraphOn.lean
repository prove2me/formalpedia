-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edgeMaximalPlanarSupergraphOn
-- name    : WilliamsonShmoys.exists_edgeMaximalPlanarSupergraphOn
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:26:50.677173+00:00
-- url     : https://prove2.me/theorems/2ebeff23-feac-456d-9810-bd2fa9ec172e
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Among the planar simple graphs on the same finite vertex type that contain M, there is one maximal under strict edge-set inclusion. This follows by maximizing edge count in the finite nonempty family; the original drawing witnesses nonemptiness, and the finite vertex type gives only finitely many simple graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edgeMaximalPlanarSupergraphOn
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N.edgeSet ⊂ P.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn P := by sorry
