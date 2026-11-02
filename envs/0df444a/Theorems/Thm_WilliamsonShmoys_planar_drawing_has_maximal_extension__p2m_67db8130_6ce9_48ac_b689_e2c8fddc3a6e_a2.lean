-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:04:29.027503+00:00
-- url     : https://prove2.me/theorems/ad7a0be6-bbd3-4bc1-9157-6cff9a8de328
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has an inclusion-maximal drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry
