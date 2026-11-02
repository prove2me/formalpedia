-- Prove2me | Theorems.Thm_planar_drawing_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
-- name    : planar_drawing_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:40.280933+00:00
-- url     : https://prove2.me/theorems/f8223507-a638-4eae-a764-723ee2646df7
-- title:
--   Finite face data for a connected planar drawing
-- statement:
--   The connected simple graph drawing with at least three vertices has finite face boundary data satisfying Euler’s relation, total boundary length twice the edge count, and minimum face boundary length three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem planar_drawing_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    ∃ f : Nat, ∃ length : Fin f → Nat,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      (∑ i : Fin f, length i) = 2 * H.edgeFinset.card ∧
      ∀ i : Fin f, 3 ≤ length i := by sorry
