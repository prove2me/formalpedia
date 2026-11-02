-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_86ac92fe_a077_498c_8a86_bf0c24de864c_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_86ac92fe_a077_498c_8a86_bf0c24de864c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:29:49.822793+00:00
-- url     : https://prove2.me/theorems/138d462c-20bd-43cc-9c59-565c454fd505
-- title:
--   Every planar drawing has an inclusion-maximal planar supergraph on the same vertices
-- statement:
--   For any finite ordered vertex type, every graph with the specified planar drawing is contained in a planar graph on the same vertices that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_86ac92fe_a077_498c_8a86_bf0c24de864c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ Q : SimpleGraph V,
      G ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        ∀ R : SimpleGraph V,
          Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q := by sorry
