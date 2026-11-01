-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_face_count__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
-- name    : WilliamsonShmoys.maximal_planar_drawing_euler_face_count__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:19.699214+00:00
-- url     : https://prove2.me/theorems/b975264c-a647-4729-9e53-57cc5272b06f
-- title:
--   Euler and triangular-face counts for maximal planar drawings
-- statement:
--   A finite drawable graph on at least three vertices that is maximal among drawable supergraphs has a face count satisfying Euler's equation and the triangular-face incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_euler_face_count__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) [DecidableRel L.Adj] (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) : ∃ f : ℕ, Fintype.card V + f = L.edgeFinset.card + 2 ∧ 3 * f = 2 * L.edgeFinset.card := by sorry
