-- Prove2me | Theorems.Thm_maximal_planar_edge_bound__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1
-- name    : maximal_planar_edge_bound__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:37:31.97017+00:00
-- url     : https://prove2.me/theorems/9248cd60-7dc5-457e-b64c-c24bd6929c95
-- title:
--   Edge bound for maximal drawable graphs
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strictly larger drawable supergraph has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem maximal_planar_edge_bound__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hV : LE.le 3 (Fintype.card V)) (hmax : ∀ M : SimpleGraph V, LE.le L M → HasPlanarDrawingOn M → M = L) : LE.le (3 * Fintype.card V) (L.edgeSet.ncard + 6) := by sorry
