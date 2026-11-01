-- Prove2me | Theorems.Thm_WilliamsonShmoys_extend_to_maximal_planar_drawing__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1
-- name    : WilliamsonShmoys.extend_to_maximal_planar_drawing__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:48.007075+00:00
-- url     : https://prove2.me/theorems/30be5ffe-46f8-47cf-a5ba-1d831971e9e1
-- title:
--   Extend a planar drawing to a maximal planar drawing
-- statement:
--   Every finite graph with the specified crossing-free drawing has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.extend_to_maximal_planar_drawing__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
