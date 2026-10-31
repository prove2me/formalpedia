-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:11:25.891333+00:00
-- url     : https://prove2.me/theorems/0b00707f-5c50-4936-bfb1-f1b2d4b20af7
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph with no proper drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2 {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : HasPlanarDrawingOn W) : ∃ H : SimpleGraph V, W ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
