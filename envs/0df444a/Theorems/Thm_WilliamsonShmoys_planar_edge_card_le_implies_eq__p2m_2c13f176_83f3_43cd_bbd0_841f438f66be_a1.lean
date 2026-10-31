-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_card_le_implies_eq__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
-- name    : WilliamsonShmoys.planar_edge_card_le_implies_eq__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:28:11.835053+00:00
-- url     : https://prove2.me/theorems/b8f11d0e-0743-447b-bd9e-0d09cae7fea7
-- title:
--   Comparable graphs with no edge-count increase are equal
-- statement:
--   If one graph is a subgraph of another on the same finite vertex type, and the latter has no more edges, then the graphs are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_card_le_implies_eq__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1 {V : Type} [Fintype V] [LinearOrder V] (K L : SimpleGraph V) (hKL : K ≤ L) (hcard : L.edgeSet.ncard ≤ K.edgeSet.ncard) : L = K := by sorry
