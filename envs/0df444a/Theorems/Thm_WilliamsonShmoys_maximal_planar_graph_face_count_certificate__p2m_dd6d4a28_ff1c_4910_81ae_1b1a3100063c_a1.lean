-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_face_count_certificate__p2m_dd6d4a28_ff1c_4910_81ae_1b1a3100063c_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_face_count_certificate__p2m_dd6d4a28_ff1c_4910_81ae_1b1a3100063c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:20:36.313015+00:00
-- url     : https://prove2.me/theorems/4d9c8971-4afd-47f0-9ee2-860519fd763e
-- title:
--   Face-count certificate for maximal planar graphs
-- statement:
--   For a drawable graph on at least three vertices that cannot be extended by any drawable edge, there is a natural number of faces satisfying Euler’s formula and the triangular-face incidence count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_face_count_certificate__p2m_dd6d4a28_ff1c_4910_81ae_1b1a3100063c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hMax : ∀ u v, u ≠ v → ¬ T.Adj u v →
      ¬ ∃ U : SimpleGraph V,
        (∀ x y, T.Adj x y → U.Adj x y) ∧
        HasPlanarDrawingOn U ∧ U.Adj u v) :
    ∃ f : Nat,
      Fintype.card V + f = T.edgeSet.ncard + 2 ∧
      3 * f = 2 * T.edgeSet.ncard := by sorry
