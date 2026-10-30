-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_euler_identity_from_maximality_42d00589
-- name    : WilliamsonShmoys.maximal_drawing_euler_identity_from_maximality_42d00589
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:01:19.832473+00:00
-- url     : https://prove2.me/theorems/a9049401-fa72-494b-9f56-c782d3c75ca3
-- title:
--   Edge-count identity for a maximal drawable graph
-- statement:
--   A finite simple graph with a crossing-free drawing that is maximal under drawable edge additions, and has at least three vertices, has exactly 3|V| − 6 edges. This child isolates the topological work needed by the parent. A proof route is to derive connectedness and triangular faces from maximality, treat the three-vertex case, and apply planar Euler and face-edge incidence formulas. These steps are the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_euler_identity_from_maximality_42d00589
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
