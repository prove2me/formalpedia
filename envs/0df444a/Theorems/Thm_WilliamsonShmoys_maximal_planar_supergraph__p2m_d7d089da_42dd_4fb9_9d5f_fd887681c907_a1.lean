-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T05:13:49.151982+00:00
-- url     : https://prove2.me/theorems/6cde1fd8-9823-4bb9-9ca3-6442511be675
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every finite planar graph on the given vertex type has a planar supergraph that is maximal under edge inclusion among planar graphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ≤ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ≤ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet = M.edgeSet := by sorry
