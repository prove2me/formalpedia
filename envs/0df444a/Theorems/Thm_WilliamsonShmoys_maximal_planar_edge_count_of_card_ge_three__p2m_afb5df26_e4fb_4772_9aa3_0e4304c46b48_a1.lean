-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_of_card_ge_three__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_of_card_ge_three__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:46.669202+00:00
-- url     : https://prove2.me/theorems/b3780c9f-7548-4d87-b8fb-1d68dbe20f67
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A planar graph on a finite linearly ordered vertex type with at least three vertices, maximal among planar graphs on that same type under inclusion, has exactly 3n−6 edges. The condition n≥3 covers the triangle boundary case. A proof proceeds from the drawing witness: maximality forces connectedness and triangular faces, after which Euler’s formula and the sum of face degrees yield the edge count. Formalizing those facts for the supplied continuous-arc drawing predicate is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_of_card_ge_three__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
