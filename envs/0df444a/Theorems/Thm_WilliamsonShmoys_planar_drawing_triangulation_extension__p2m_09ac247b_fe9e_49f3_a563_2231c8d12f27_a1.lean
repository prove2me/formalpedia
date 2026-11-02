-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_09ac247b_fe9e_49f3_a563_2231c8d12f27_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_09ac247b_fe9e_49f3_a563_2231c8d12f27_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:17:50.164811+00:00
-- url     : https://prove2.me/theorems/067ebb73-e756-4640-b5cf-ef3a010c6f28
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every finite simple graph with at least three vertices that has the specified crossing-free drawing is a subgraph of a graph on the same vertices that also has such a drawing and has exactly 3|V|−6 edges. The child packages the geometric triangulation step together with the resulting edge-count comparison.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_09ac247b_fe9e_49f3_a563_2231c8d12f27_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      (∀ u v, Q.Adj u v → R.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      (letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
       letI : DecidableRel R.Adj := Classical.decRel R.Adj
       Q.edgeFinset.card ≤ R.edgeFinset.card) ∧
      (letI : DecidableRel R.Adj := Classical.decRel R.Adj
       R.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
