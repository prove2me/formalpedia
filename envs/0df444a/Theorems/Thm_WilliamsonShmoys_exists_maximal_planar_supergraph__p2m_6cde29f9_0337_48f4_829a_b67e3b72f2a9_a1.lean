-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:35.746418+00:00
-- url     : https://prove2.me/theorems/db4df47a-bf70-4441-a49c-541f2ec7acbf
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1 {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet ∧
      HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V, U.edgeSet ⊆ W.edgeSet →
        HasPlanarDrawingOn W → U.edgeSet = W.edgeSet := by
  sorry
