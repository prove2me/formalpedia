-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:27.318984+00:00
-- url     : https://prove2.me/theorems/11371f3f-0d50-4c49-9eed-89dfd5ac185f
-- title:
--   Finite maximal planar extension
-- statement:
--   Every finite graph with a crossing-free drawing is contained in an inclusion-maximal graph on the same vertices that has a crossing-free drawing; the extension has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1 {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) : ∃ H : SimpleGraph V, (∀ ⦃u v : V⦄, Z.Adj u v → H.Adj u v) ∧ Z.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
