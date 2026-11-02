-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_extension_maximizing_edge_count__p2m_3721485b_3cdc_4a3e_9978_b518aa3e9dbd_a1
-- name    : WilliamsonShmoys.exists_drawable_extension_maximizing_edge_count__p2m_3721485b_3cdc_4a3e_9978_b518aa3e9dbd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:38:55.720633+00:00
-- url     : https://prove2.me/theorems/df2edb60-5525-4987-92df-68b64db928cc
-- title:
--   A drawable extension maximizing edge count
-- statement:
--   Among drawable supergraphs of a given drawable graph on a finite ordered vertex type, there is one whose edge set has maximal cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_drawable_extension_maximizing_edge_count__p2m_3721485b_3cdc_4a3e_9978_b518aa3e9dbd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, L ≤ U → HasPlanarDrawingOn U →
        Nat.card U.edgeSet ≤ Nat.card T.edgeSet := by
  sorry
