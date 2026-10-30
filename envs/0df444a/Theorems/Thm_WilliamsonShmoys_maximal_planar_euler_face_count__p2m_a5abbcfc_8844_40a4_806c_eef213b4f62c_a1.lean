-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_count__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
-- name    : WilliamsonShmoys_maximal_planar_euler_face_count__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:52:56.153449+00:00
-- url     : https://prove2.me/theorems/acc0ec2a-7681-4a4b-b29d-c928de95ce10
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected graph with the specified planar drawing, the vertex count, edge count, and number of faces satisfy Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_euler_face_count__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
