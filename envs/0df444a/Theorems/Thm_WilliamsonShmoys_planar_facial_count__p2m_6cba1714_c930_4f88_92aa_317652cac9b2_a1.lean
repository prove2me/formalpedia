-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_facial_count__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
-- name    : WilliamsonShmoys.planar_facial_count__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:37.502258+00:00
-- url     : https://prove2.me/theorems/2930c541-cd90-4895-988f-c75e47ffb674
-- title:
--   Euler and triangular face counts for a maximal planar drawing
-- statement:
--   For a maximal planar drawing of a finite simple graph with at least three vertices, the number of faces satisfies Euler's equation, and every face is triangular, so face-edge incidences are counted three per face and twice per edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_facial_count__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by sorry
