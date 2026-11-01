-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_extension__p2m_1ac9c334_525d_486c_82db_79a23d6eb9e0_a2
-- name    : WilliamsonShmoys.exists_maximal_simpleGraph_extension__p2m_1ac9c334_525d_486c_82db_79a23d6eb9e0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:58:26.850986+00:00
-- url     : https://prove2.me/theorems/4a9cdddb-d343-412e-b0c3-fb8d032a2a29
-- title:
--   Finite maximal simple graph extension for a predicate
-- statement:
--   For a finite vertex type, any graph satisfying a predicate has a predicate-satisfying supergraph with at least as many edges that is maximal among predicate-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_simpleGraph_extension__p2m_1ac9c334_525d_486c_82db_79a23d6eb9e0_a2
    {V : Type} [Fintype V]
    (N : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P N) :
    ∃ M : SimpleGraph V,
      N.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      N ≤ M ∧
      P M ∧
      (∀ M' : SimpleGraph V, M ≤ M' → P M' → M' = M) := by
  sorry
