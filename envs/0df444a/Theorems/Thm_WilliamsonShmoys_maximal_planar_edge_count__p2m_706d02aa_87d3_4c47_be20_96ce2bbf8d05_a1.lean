-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:09:20.940849+00:00
-- url     : https://prove2.me/theorems/e5af1f58-1baf-49a9-bfe1-0313f8cb5edc
-- title:
--   Count the edges of a maximal planar graph
-- statement:
--   A maximal simple graph with the supplied crossing-free drawing and at least three vertices has exactly `3 * |V| - 6` edges. A proof route is to show maximality forces every face in the induced plane embedding to be triangular, then apply Euler’s formula and count edge-face incidences. The lower boundary `|V| = 3` is included; the result should not be extended to smaller vertex sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
