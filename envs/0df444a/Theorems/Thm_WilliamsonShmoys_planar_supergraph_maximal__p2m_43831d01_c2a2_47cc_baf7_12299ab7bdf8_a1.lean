-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:18.08299+00:00
-- url     : https://prove2.me/theorems/3647f07c-750e-4c3e-8be8-ca29b1e4d823
-- title:
--   Extend a planar drawing to an edge-maximal planar supergraph
-- statement:
--   Extend the given drawing to a planar supergraph on the same finite vertex set that has no proper planar supergraph on that vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 <= Fintype.card V) : ∃ H : SimpleGraph V, K <= H ∧ HasPlanarDrawingOn H ∧ (∀ J : SimpleGraph V, H <= J → HasPlanarDrawingOn J → J <= H) := by sorry
