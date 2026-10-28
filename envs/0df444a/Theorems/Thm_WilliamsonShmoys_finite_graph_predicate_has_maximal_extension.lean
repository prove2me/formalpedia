-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_predicate_has_maximal_extension
-- name    : WilliamsonShmoys.finite_graph_predicate_has_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:47:19.07446+00:00
-- url     : https://prove2.me/theorems/4995b88d-5487-4f4d-9cf8-b4ff51e04fdc
-- title:
--   Finite simple graphs have predicate-maximal extensions
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, every graph satisfying the predicate has an extension that is maximal among predicate-satisfying extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_predicate_has_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (N : SimpleGraph V) (hP : P N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
