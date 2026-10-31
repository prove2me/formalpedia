-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximum_edge_count_implies_target_properties__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
-- name    : WilliamsonShmoys.maximum_edge_count_implies_target_properties__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:14:14.452983+00:00
-- url     : https://prove2.me/theorems/f2245cfe-f25c-448c-acd1-545fce7cd6cf
-- title:
--   Edge maximum implies inclusion maximality and the edge lower bound
-- statement:
--   If M extends L and has at least as many edges as every drawable extension of L, then no drawable graph can properly extend M, and L's edgeFinset cardinality is at most M's edgeSet cardinality. Prove this using inclusion and finite-set cardinality, keeping the target's explicit decidable adjacency instance for L.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximum_edge_count_implies_target_properties__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L M : SimpleGraph V)
    (hLM : L ≤ M)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       L.edgeFinset.card ≤ M.edgeSet.ncard) := by sorry
