-- Prove2me | Theorems.Thm_finite_simpleGraph_supergraph_maximal_for_predicate
-- name    : finite_simpleGraph_supergraph_maximal_for_predicate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:09:48.083256+00:00
-- url     : https://prove2.me/theorems/635347ec-cad7-442d-b690-04d47785a578
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   On a finite vertex type, any graph satisfying a predicate has a supergraph satisfying that predicate which is maximal among predicate-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem finite_simpleGraph_supergraph_maximal_for_predicate
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K = H) := by sorry
