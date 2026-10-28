-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_maximal_extension
-- name    : WilliamsonShmoys.finite_simpleGraph_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:29:12.418736+00:00
-- url     : https://prove2.me/theorems/2aa8b5fb-dfa6-402f-af11-0c733b71a3bc
-- title:
--   Maximal property-preserving extension of a finite simple graph
-- statement:
--   For a finite vertex type, any graph satisfying a predicate has a supergraph satisfying that predicate which is maximal among predicate-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.finite_simpleGraph_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧
      ∀ J : SimpleGraph V, H ≤ J → P J → J = H := by sorry
