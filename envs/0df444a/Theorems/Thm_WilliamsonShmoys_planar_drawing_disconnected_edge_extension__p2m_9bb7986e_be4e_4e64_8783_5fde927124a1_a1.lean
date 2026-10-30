-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_edge_extension__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
-- name    : WilliamsonShmoys.planar_drawing_disconnected_edge_extension__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:52.04199+00:00
-- url     : https://prove2.me/theorems/a5eabcd9-06a0-40fd-b7d2-c42404f6d529
-- title:
--   Strict planar extension of a disconnected drawing
-- statement:
--   Every disconnected drawable graph on at least three vertices has a strict drawable supergraph on the same vertices. This is the geometric extension step used to rule out disconnected maximal drawable supergraphs. Prove it by separating the drawings of components and adding an arc between two components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_disconnected_edge_extension__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K' ≠ K := by sorry
