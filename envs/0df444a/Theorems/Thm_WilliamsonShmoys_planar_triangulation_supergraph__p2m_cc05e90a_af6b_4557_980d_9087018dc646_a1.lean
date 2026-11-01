-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph__p2m_cc05e90a_af6b_4557_980d_9087018dc646_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph__p2m_cc05e90a_af6b_4557_980d_9087018dc646_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:26:53.570838+00:00
-- url     : https://prove2.me/theorems/e31b05a7-4e78-4789-8a19-ecdeedbcdfa7
-- title:
--   Triangulated drawable supergraph on the same vertex set
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained, on that same vertex set, in a drawable graph with exactly 3|V|−6 edges. This removes the maximality and edge-count bookkeeping from the parent; triangulating the faces and applying Euler’s formula is the independent proof route. The remaining core is formalizing planar augmentation and the face count for the given arc-based drawing predicate. The three-vertex boundary is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_supergraph__p2m_cc05e90a_af6b_4557_980d_9087018dc646_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj
         N.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
