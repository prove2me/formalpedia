-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_max_pair_count__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
-- name    : WilliamsonShmoys.exists_planar_supergraph_max_pair_count__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:02:01.64+00:00
-- url     : https://prove2.me/theorems/6dfe235c-2d93-4cd3-a1e8-c2011cbaaa57
-- title:
--   A drawable supergraph maximizing adjacent-pair count exists
-- statement:
--   Among drawable supergraphs of H, one maximizes the number of ordered adjacent vertex pairs. The subtype cardinality is defined without requiring decidable adjacency in the theorem statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_max_pair_count__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → Nat.card {p : V × V // M.Adj p.1 p.2} ≤ Nat.card {p : V × V // L.Adj p.1 p.2} := by sorry
