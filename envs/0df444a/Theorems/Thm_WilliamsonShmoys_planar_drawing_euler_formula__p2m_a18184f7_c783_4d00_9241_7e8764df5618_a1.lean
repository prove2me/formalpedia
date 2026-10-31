-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_formula__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:49:08.864994+00:00
-- url     : https://prove2.me/theorems/deb60313-bf19-49db-b390-149a9da32a24
-- title:
--   Euler formula for a connected planar drawing
-- statement:
--   A finite connected graph with the supplied planar drawing has a natural-number face count satisfying Euler’s formula. This is the Euler component of the target; its proof route is to interpret the drawing as a plane embedding and apply the connected planar graph Euler formula, including for trees and embeddings with bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_formula__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected) :
    ∃ f : ℕ,
      (Fintype.card V : ℤ) - (M.edgeFinset.card : ℤ) + (f : ℤ) = 2 := by sorry
