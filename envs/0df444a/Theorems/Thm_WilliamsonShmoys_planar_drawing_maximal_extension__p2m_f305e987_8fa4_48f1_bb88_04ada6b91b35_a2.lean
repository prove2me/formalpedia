-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2
-- name    : WilliamsonShmoys_planar_drawing_maximal_extension__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:29:08.059891+00:00
-- url     : https://prove2.me/theorems/fcae0d51-0352-45f3-bf24-4110581dd971
-- title:
--   Every finite planar drawing has a maximal planar supergraph
-- statement:
--   Extend the given planar graph to a planar supergraph on the same finite vertex type that has no strictly larger planar supergraph on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_planar_drawing_maximal_extension__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
      ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G := by
  sorry
