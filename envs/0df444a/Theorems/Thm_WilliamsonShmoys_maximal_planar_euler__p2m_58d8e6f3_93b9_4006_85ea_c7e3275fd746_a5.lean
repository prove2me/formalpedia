-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
-- name    : WilliamsonShmoys.maximal_planar_euler__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:00:12.40791+00:00
-- url     : https://prove2.me/theorems/d40a2e36-a36d-4b2e-986d-2d20df82bdb3
-- title:
--   Euler face count for an inclusion-maximal planar drawing
-- statement:
--   For a drawable graph with at least three vertices that has no proper drawable supergraph on the same vertex type, there is a face count satisfying Euler’s equation. The proof route establishes connectedness, obtains a plane embedding from the drawing arcs, and applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_euler__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by sorry
