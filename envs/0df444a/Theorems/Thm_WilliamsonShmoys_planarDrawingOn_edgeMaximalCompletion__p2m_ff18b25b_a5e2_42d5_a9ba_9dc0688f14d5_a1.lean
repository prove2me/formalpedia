-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeMaximalCompletion__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
-- name    : WilliamsonShmoys.planarDrawingOn_edgeMaximalCompletion__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:23:17.922597+00:00
-- url     : https://prove2.me/theorems/253069e0-57f5-47cb-9309-71b399985e4e
-- title:
--   Finite edge-maximal drawable supergraph
-- statement:
--   Every drawable finite graph on a fixed ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_edgeMaximalCompletion__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ K' : SimpleGraph V, K ≤ K' ∧ HasPlanarDrawingOn K' ∧
      ∀ H : SimpleGraph V, K' ≤ H → HasPlanarDrawingOn H → H = K' := by sorry
