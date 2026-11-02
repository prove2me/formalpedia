-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_exists__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1
-- name    : WilliamsonShmoys.maximal_drawable_extension_exists__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:21:32.830756+00:00
-- url     : https://prove2.me/theorems/ae302955-1ccc-4f25-af9e-48597b94b038
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertex set that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension_exists__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by sorry
