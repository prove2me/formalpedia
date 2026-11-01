-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_edge_drawable_extension__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1
-- name    : WilliamsonShmoys.exists_max_edge_drawable_extension__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:28.21694+00:00
-- url     : https://prove2.me/theorems/07123160-8e02-4c14-a3ba-8b97213ab1a9
-- title:
--   A drawable extension with maximum edge count
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph whose edge count is at least that of every other drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_edge_drawable_extension__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L → Nat.card {e : Sym2 V // e ∈ L.edgeSet} ≤ Nat.card {e : Sym2 V // e ∈ K.edgeSet} := by sorry
