-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_152d6993_7004_4697_ab26_f8c2f883dc25_a1
-- name    : WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_152d6993_7004_4697_ab26_f8c2f883dc25_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:54.267728+00:00
-- url     : https://prove2.me/theorems/ba617e25-272f-480b-8c9f-e5a82d8e4502
-- title:
--   Triangulating extension of a finite planar drawing
-- statement:
--   Every finite drawable simple graph with at least three vertices is contained, on the same vertex set, in a drawable simple graph with exactly 3n − 6 edges. The proof augments a planar embedding to a triangulation and applies Euler’s formula and the triangular face-edge incidence count; it must handle disconnected drawings and the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_152d6993_7004_4697_ab26_f8c2f883dc25_a1 {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V, M ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
      S.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
