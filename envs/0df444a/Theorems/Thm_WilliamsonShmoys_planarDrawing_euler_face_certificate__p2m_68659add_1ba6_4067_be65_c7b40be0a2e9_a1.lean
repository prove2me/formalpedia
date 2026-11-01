-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_face_certificate__p2m_68659add_1ba6_4067_be65_c7b40be0a2e9_a1
-- name    : WilliamsonShmoys.planarDrawing_euler_face_certificate__p2m_68659add_1ba6_4067_be65_c7b40be0a2e9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:06.297296+00:00
-- url     : https://prove2.me/theorems/fc75ed8d-2c02-4ee5-b600-f137d709d1e3
-- title:
--   Euler face certificate for a connected planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a natural-number face count satisfying Euler’s formula and the bound that three times the number of faces is at most twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_euler_face_certificate__p2m_68659add_1ba6_4067_be65_c7b40be0a2e9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 ∧
      3 * f ≤ 2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) := by sorry
