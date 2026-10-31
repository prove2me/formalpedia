-- Prove2me | Theorems.Thm_planarDrawing_completion_edge_count__p2m_9248cd60_7dc5_457e_b64c_c24bd6929c95_a2
-- name    : planarDrawing_completion_edge_count__p2m_9248cd60_7dc5_457e_b64c_c24bd6929c95_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:15.50226+00:00
-- url     : https://prove2.me/theorems/669c86c2-d502-40df-b2a7-d12de81131b5
-- title:
--   Triangulating completion of a finite planar drawing
-- statement:
--   Any finite graph with a crossing-free drawing and at least three vertices can be extended, without adding vertices, to a crossing-free graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem planarDrawing_completion_edge_count__p2m_9248cd60_7dc5_457e_b64c_c24bd6929c95_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hV : LE.le 3 (Fintype.card V)) : ∃ M : SimpleGraph V, LE.le L M ∧ HasPlanarDrawingOn M ∧ 3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
