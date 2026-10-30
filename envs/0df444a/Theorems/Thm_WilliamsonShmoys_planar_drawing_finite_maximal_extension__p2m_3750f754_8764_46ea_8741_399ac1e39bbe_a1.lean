-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension__p2m_3750f754_8764_46ea_8741_399ac1e39bbe_a1
-- name    : WilliamsonShmoys.planar_drawing_finite_maximal_extension__p2m_3750f754_8764_46ea_8741_399ac1e39bbe_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:50.841909+00:00
-- url     : https://prove2.me/theorems/f2239872-da14-4fcd-a2f9-08c413d80af1
-- title:
--   A finite planar graph has a maximal planar supergraph
-- statement:
--   Every planar graph on a finite vertex type has a planar supergraph that admits no strictly larger planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_finite_maximal_extension__p2m_3750f754_8764_46ea_8741_399ac1e39bbe_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by
  sorry
