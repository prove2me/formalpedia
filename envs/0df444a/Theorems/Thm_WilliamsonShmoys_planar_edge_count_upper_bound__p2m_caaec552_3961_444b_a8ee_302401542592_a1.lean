-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_caaec552_3961_444b_a8ee_302401542592_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_caaec552_3961_444b_a8ee_302401542592_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:39:45.001346+00:00
-- url     : https://prove2.me/theorems/38c95c82-19cb-4f35-865d-2ac0628174cb
-- title:
--   Planar edge count upper bound
-- statement:
--   Every graph with a drawing as defined in the imported planar-drawing definition, on at least three vertices, has at most three times the number of vertices minus six edges. This is the Euler upper-bound step; a proof can reduce to connected components and apply the planar Euler inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_caaec552_3961_444b_a8ee_302401542592_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    G.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
