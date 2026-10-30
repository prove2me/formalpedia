-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edgeSet_ncard_mono__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1
-- name    : WilliamsonShmoys_planar_edgeSet_ncard_mono__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:06.928016+00:00
-- url     : https://prove2.me/theorems/8ed16852-7d8e-4cb1-9123-be4a9eb367cc
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite vertex types, including a simple graph in another cannot decrease its number of edges. This removes the finite-set monotonicity step from the parent; it can be proved by showing edgeSet inclusion from adjacency inclusion and applying finite cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_edgeSet_ncard_mono__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1 {V : Type} [Fintype V] (G H : SimpleGraph V) (hsub : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
