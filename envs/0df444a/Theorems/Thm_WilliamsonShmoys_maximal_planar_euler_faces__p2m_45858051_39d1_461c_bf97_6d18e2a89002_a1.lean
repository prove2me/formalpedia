-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_faces__p2m_45858051_39d1_461c_bf97_6d18e2a89002_a1
-- name    : WilliamsonShmoys.maximal_planar_euler_faces__p2m_45858051_39d1_461c_bf97_6d18e2a89002_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:37:15.719994+00:00
-- url     : https://prove2.me/theorems/dd78c457-06f8-4973-886c-d0aede564096
-- title:
--   Euler relation for a maximal planar drawing
-- statement:
--   For a maximal planar drawing on at least three vertices, there is a face count satisfying the Euler relation E + 2 = |V| + f.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_euler_faces__p2m_45858051_39d1_461c_bf97_6d18e2a89002_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    ∃ f : ℕ, H.edgeSet.ncard + 2 = Fintype.card V + f := by sorry
