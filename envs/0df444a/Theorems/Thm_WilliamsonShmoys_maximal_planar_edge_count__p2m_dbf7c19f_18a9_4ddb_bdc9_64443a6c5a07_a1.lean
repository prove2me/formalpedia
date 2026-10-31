-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:19:04.696241+00:00
-- url     : https://prove2.me/theorems/7a456d63-5ec6-4840-a69c-b6d30bc6b909
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hLmax : ∀ M : SimpleGraph V, LE.le L M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
