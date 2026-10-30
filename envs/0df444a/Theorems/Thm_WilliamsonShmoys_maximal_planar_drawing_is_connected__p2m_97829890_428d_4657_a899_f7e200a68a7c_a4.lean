-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_is_connected__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4
-- name    : WilliamsonShmoys.maximal_planar_drawing_is_connected__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:27:24.323559+00:00
-- url     : https://prove2.me/theorems/8603d9a1-7393-4bbf-851c-41d8426e3226
-- title:
--   A maximal planar drawing is connected
-- statement:
--   A maximal drawable graph on at least three vertices is connected. This isolates the geometric work from the parent: prove that a disconnected drawing admits a drawable strict supergraph, for example by constructing a suitable arc through a face of the embedding. The unresolved core is formalizing that construction under the exact arc-intersection conditions, including nested components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_is_connected__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.Connected := by sorry
