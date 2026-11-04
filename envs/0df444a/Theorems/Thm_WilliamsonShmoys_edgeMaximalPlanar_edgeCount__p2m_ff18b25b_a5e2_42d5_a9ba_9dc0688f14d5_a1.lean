-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_edgeCount__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
-- name    : WilliamsonShmoys.edgeMaximalPlanar_edgeCount__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:23:32.171716+00:00
-- url     : https://prove2.me/theorems/4c527512-1622-4d01-a868-d6bc284410d2
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges, for any decidable-adjacency instance.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edgeMaximalPlanar_edgeCount__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H = K)
    (hn : 3 ≤ Fintype.card V) :
    ∀ [DecidableRel K.Adj], K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
