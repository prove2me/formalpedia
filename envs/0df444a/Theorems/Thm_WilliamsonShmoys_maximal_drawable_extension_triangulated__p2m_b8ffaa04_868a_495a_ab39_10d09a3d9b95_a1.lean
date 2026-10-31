-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_triangulated__p2m_b8ffaa04_868a_495a_ab39_10d09a3d9b95_a1
-- name    : WilliamsonShmoys.maximal_drawable_extension_triangulated__p2m_b8ffaa04_868a_495a_ab39_10d09a3d9b95_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:22.031464+00:00
-- url     : https://prove2.me/theorems/6e736750-a362-4363-844e-e38c08b33ed2
-- title:
--   Triangulated extension of a finite drawable graph
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges. The condition n≥3 is needed for the planar triangulation edge count; retaining all vertices permits the parent to apply its maximality hypothesis directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension_triangulated__p2m_b8ffaa04_868a_495a_ab39_10d09a3d9b95_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (_hKdec : DecidableRel K.Adj),
      M ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
