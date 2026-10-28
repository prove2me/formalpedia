-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_f3620a14
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition_f3620a14
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:10:26.359383+00:00
-- url     : https://prove2.me/theorems/483fa642-71bc-43cb-a292-d46b685f0ee3
-- title:
--   Euler and face-incidence equations for a maximal planar drawing
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition_f3620a14
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S → T ≤ S → S ≤ T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = T.edgeSet.ncard + 2 ∧
      3 * f = 2 * T.edgeSet.ncard := by sorry
