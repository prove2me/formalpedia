-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:50:13.35809+00:00
-- url     : https://prove2.me/theorems/26683b08-836c-419a-b063-0a6c5666eed9
-- title:
--   Edge bound for a finite topological planar drawing
-- statement:
--   Every simple graph with at least three vertices that has a drawing satisfying `HasPlanarDrawingOn` has at most `3|V| − 6` edges. This is the Euler upper-bound half of the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
     H.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  sorry
