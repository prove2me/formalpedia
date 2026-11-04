-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion__p2m_ae2deb14_265a_4589_b20a_d2c312b9c2e6_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulated_completion__p2m_ae2deb14_265a_4589_b20a_d2c312b9c2e6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:36:09.519572+00:00
-- url     : https://prove2.me/theorems/1ccfbc5e-ee72-4561-8bb6-ab9cee0a3a68
-- title:
--   Triangulated completion of a drawable simple graph
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing can be extended, on the same vertex set, to a crossing-free simple graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulated_completion__p2m_ae2deb14_265a_4589_b20a_d2c312b9c2e6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn G) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
