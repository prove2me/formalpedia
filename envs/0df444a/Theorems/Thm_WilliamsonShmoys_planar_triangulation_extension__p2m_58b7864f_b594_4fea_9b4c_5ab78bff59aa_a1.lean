-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_58b7864f_b594_4fea_9b4c_5ab78bff59aa_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_58b7864f_b594_4fea_9b4c_5ab78bff59aa_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:13:12.680807+00:00
-- url     : https://prove2.me/theorems/10fbf93e-9f1f-430c-8d69-9a023f7a87fc
-- title:
--   Planar triangulation extension with fixed vertex set
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex set of size at least three has a drawable supergraph on that same vertex set whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_58b7864f_b594_4fea_9b4c_5ab78bff59aa_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeFinset ⊆ N.edgeFinset ∧
      N.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
