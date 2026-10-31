-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_f1bb3fc5_14ed_4f61_8573_9a7a487e7a06_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_f1bb3fc5_14ed_4f61_8573_9a7a487e7a06_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:56.319128+00:00
-- url     : https://prove2.me/theorems/fc475467-cefd-44fd-810b-5d1d49565f31
-- title:
--   Planar graph triangulation completion
-- statement:
--   Every simple graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a planar supergraph on the same vertices whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_f1bb3fc5_14ed_4f61_8573_9a7a487e7a06_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ 3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
