-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulating_supergraph__p2m_f289c5f6_bcae_4951_8202_39fcc0f6c95e_a1
-- name    : WilliamsonShmoys.planar_triangulating_supergraph__p2m_f289c5f6_bcae_4951_8202_39fcc0f6c95e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:56.229482+00:00
-- url     : https://prove2.me/theorems/903afd89-6ff0-4c8d-a56d-218ccc22cf30
-- title:
--   Triangulating supergraph for a planar drawing
-- statement:
--   Every graph with a crossing-free drawing on at least three fixed vertices is a subgraph of a crossing-free graph on the same vertices with exactly 3|V|−6 edges. The count monotonicity is included for the parent reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulating_supergraph__p2m_f289c5f6_bcae_4951_8202_39fcc0f6c95e_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) : ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ M.edgeSet.ncard ≤ N.edgeSet.ncard ∧ N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
