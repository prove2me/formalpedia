-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_on
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:56:27.314243+00:00
-- url     : https://prove2.me/theorems/7a1aac6b-ea3c-446e-ba04-a38db13cde0b
-- title:
--   Existence of a maximal planar supergraph on a fixed vertex set
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertex type. This removes the maximality-selection step from the parent. Prove it by maximizing edge count among drawable supergraphs and restricting the original drawing when edges are removed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_on
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKplanar : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ IsMaximalPlanarOn H := by sorry
