-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_augmentation__p2m_ef7f67a4_b20c_4576_8674_97edcb1c6ef4_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_ef7f67a4_b20c_4576_8674_97edcb1c6ef4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:32:02.41189+00:00
-- url     : https://prove2.me/theorems/39c8b022-a293-476d-807d-cfc1fb68c035
-- title:
--   Triangulated planar completion on the same vertex set
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex set of size at least three is a subgraph of a drawable graph on the same vertices having exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_ef7f67a4_b20c_4576_8674_97edcb1c6ef4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    (letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
     ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
