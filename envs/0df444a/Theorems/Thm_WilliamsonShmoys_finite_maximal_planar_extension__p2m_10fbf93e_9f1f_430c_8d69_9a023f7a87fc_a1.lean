-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
-- name    : WilliamsonShmoys.finite_maximal_planar_extension__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:49.406335+00:00
-- url     : https://prove2.me/theorems/0195b79c-f96f-4126-8caa-2fda6843d87e
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable extension on the same vertices that admits no proper drawable extension. The proof route is to maximize edge count over the finite family of simple graphs containing M that admit a drawing; the family is nonempty because it contains M.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_planar_extension__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeFinset ⊆ N.edgeFinset ∧
      ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn K →
        N.edgeFinset ⊆ K.edgeFinset →
        K.edgeFinset ⊆ N.edgeFinset := by sorry
