-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
-- name    : WilliamsonShmoys.maximal_drawable_extension__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:05:33.51181+00:00
-- url     : https://prove2.me/theorems/c7758452-5c88-40df-afb8-de29ffe25650
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that contains every drawable supergraph of itself; equivalently, it is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ∀ u v, L.Adj u v → K.Adj u v) := by sorry
