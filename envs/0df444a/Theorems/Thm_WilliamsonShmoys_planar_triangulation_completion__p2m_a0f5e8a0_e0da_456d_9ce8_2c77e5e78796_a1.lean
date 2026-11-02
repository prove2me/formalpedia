-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_a0f5e8a0_e0da_456d_9ce8_2c77e5e78796_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_a0f5e8a0_e0da_456d_9ce8_2c77e5e78796_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:51:18.424856+00:00
-- url     : https://prove2.me/theorems/e3eb1401-8114-44d9-870e-95a93988f448
-- title:
--   Planar triangulation completion with exact edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices extends, on the same vertex set, to a drawable supergraph with exactly 3|V|−6 edges. The condition n ≥ 3 is essential to the triangulation count; at n = 3 the completion is the triangle. The proof route is finite edge augmentation followed by triangular-face and Euler counting. This isolates the topological completion and counting work from the parent’s maximality argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_a0f5e8a0_e0da_456d_9ce8_2c77e5e78796_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      HasPlanarDrawingOn L ∧
      (∀ u v, G.Adj u v → L.Adj u v) ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj; 3 * Fintype.card V = L.edgeFinset.card + 6) := by sorry
