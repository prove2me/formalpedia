-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_completion__p2m_953852c9_9877_4510_aaba_a6b57c23a189_a4
-- name    : WilliamsonShmoys.planar_drawing_euler_completion__p2m_953852c9_9877_4510_aaba_a6b57c23a189_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T00:31:38.141255+00:00
-- url     : https://prove2.me/theorems/c2b3e217-3914-41f8-91f1-9925fc5a7d71
-- title:
--   Euler-count planar completion on the same vertex set
-- statement:
--   Any finite simple graph with at least three vertices and a crossing-free drawing can be extended, without changing its vertex set, to a crossing-free graph whose edge count satisfies the planar Euler equality. This removes the geometric and Euler-counting work from the parent, which then needs only edge-set monotonicity and arithmetic. A concrete independent proof route is finite maximal edge extension of the drawing, followed by the fact that every face of a maximal planar drawing has three boundary edges and Euler’s formula. The remaining core obligation is to formalize this topological completion and face-count argument for the supplied arc-based drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Finite

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_completion__p2m_953852c9_9877_4510_aaba_a6b57c23a189_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
