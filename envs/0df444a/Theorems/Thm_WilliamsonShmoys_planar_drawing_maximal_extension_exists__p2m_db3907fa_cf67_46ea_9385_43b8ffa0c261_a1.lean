-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:57:47.820646+00:00
-- url     : https://prove2.me/theorems/4cfdce90-033b-4688-accf-ee5789518668
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertices that is maximal under edge inclusion. This follows by maximizing edge count among the finite collection of drawable supergraphs; it preserves the original drawing predicate and handles the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ N : SimpleGraph V,
        H.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet ⊆ H.edgeSet := by sorry
