-- Prove2me | Theorems.Thm_finite_graph_family_has_edgeSet_maximal__p2m_589dfbf2_6752_446d_86dd_1ad54b42e363_a1
-- name    : finite_graph_family_has_edgeSet_maximal__p2m_589dfbf2_6752_446d_86dd_1ad54b42e363_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:26:55.358425+00:00
-- url     : https://prove2.me/theorems/c570f396-08d3-4b7a-a566-4e4b587bbde3
-- title:
--   A finite family of graphs has an edge-inclusion-maximal member
-- statement:
--   For any nonempty family of simple graphs on a finite linearly ordered vertex type, some member has no strictly larger edge set among the family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem finite_graph_family_has_edgeSet_maximal__p2m_589dfbf2_6752_446d_86dd_1ad54b42e363_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (hP : ∃ G, P G) :
    ∃ H : SimpleGraph V, P H ∧
      ∀ K : SimpleGraph V, P K → H.edgeSet ⊆ K.edgeSet →
        H.edgeSet = K.edgeSet := by
  sorry
