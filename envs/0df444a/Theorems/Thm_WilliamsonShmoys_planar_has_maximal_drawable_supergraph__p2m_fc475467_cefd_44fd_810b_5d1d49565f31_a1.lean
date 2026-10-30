-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_has_maximal_drawable_supergraph__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1
-- name    : WilliamsonShmoys.planar_has_maximal_drawable_supergraph__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:52:11.816483+00:00
-- url     : https://prove2.me/theorems/aaf1876f-778c-4596-8ed5-7b56263fc60a
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. The proof route is to choose a maximal element from the finite set of simple graphs on V, using K as a drawable member.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_has_maximal_drawable_supergraph__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
