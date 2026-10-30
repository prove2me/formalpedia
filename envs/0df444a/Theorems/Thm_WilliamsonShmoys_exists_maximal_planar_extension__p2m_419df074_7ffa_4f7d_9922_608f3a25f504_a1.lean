-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:20.210479+00:00
-- url     : https://prove2.me/theorems/cd9a71e9-3fb8-46b9-a739-43fa7ef62fe6
-- title:
--   Existence of a maximal planar extension
-- statement:
--   Every finite planar graph on the given vertex type has a planar supergraph on that same vertex type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ H' : SimpleGraph V, H ≤ H' ∧ WilliamsonShmoys.HasPlanarDrawingOn H' ∧ (∀ K : SimpleGraph V, H' ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H') := by sorry
