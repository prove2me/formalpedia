-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_to_planarMapDataExtension__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
-- name    : WilliamsonShmoys.planarDrawingOn_to_planarMapDataExtension__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:44:13.544865+00:00
-- url     : https://prove2.me/theorems/b3eca2bb-f78b-4222-b8fc-fe99bf34c163
-- title:
--   Extend a planar drawing to connected finite face data
-- statement:
--   A crossing-free drawing of a finite graph with at least three vertices can be extended, by adding edges on the same vertex set, to a connected planar graph carrying the supplied finite face data. The output graph contains every original edge. The size hypothesis preserves the target’s boundary cases, including disconnected graphs and isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_to_planarMapDataExtension__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 <= Fintype.card V) :
    ∃ (K : SimpleGraph V) (hK : DecidableRel K.Adj),
      (∀ ⦃u v : V⦄, J.Adj u v → K.Adj u v) ∧
      Nonempty (@PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 V (inferInstance) K hK) := by sorry
