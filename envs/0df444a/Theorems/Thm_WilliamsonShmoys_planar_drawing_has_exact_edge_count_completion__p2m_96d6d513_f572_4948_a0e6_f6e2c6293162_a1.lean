-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_96d6d513_f572_4948_a0e6_f6e2c6293162_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_96d6d513_f572_4948_a0e6_f6e2c6293162_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:33:31.197117+00:00
-- url     : https://prove2.me/theorems/7ac292bd-eb81-4fbd-9c7b-9e536c56a231
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_96d6d513_f572_4948_a0e6_f6e2c6293162_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hCard : Nat.le 3 (Fintype.card V)) (hK : HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      And (Set.Subset K.edgeSet H.edgeSet)
        (And (HasPlanarDrawingOn H)
          (H.edgeSet.ncard = 3 * Fintype.card V - 6)) := by
  sorry
