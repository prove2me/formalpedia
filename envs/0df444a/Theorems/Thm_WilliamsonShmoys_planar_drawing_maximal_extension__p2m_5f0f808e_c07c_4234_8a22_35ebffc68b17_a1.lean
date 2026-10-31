-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:43:21.021867+00:00
-- url     : https://prove2.me/theorems/19232441-686a-4272-ba92-bbecb802c741
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices. This isolates the finite selection step from the topological edge-count argument. A proof route is to maximize the edge-set cardinality among drawable supergraphs of K; any strict drawable extension would have more edges. The original drawing itself witnesses that this finite family is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ L : SimpleGraph V, H ≤ L → L ≠ H → ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by
  sorry
