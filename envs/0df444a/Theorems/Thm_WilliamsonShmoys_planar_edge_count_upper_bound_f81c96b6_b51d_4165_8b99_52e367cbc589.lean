-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_f81c96b6_b51d_4165_8b99_52e367cbc589
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_f81c96b6_b51d_4165_8b99_52e367cbc589
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:25:26.660982+00:00
-- url     : https://prove2.me/theorems/01e69ab3-12df-4a2d-8d88-df663cdc6d8e
-- title:
--   Planar edge count upper bound for this target
-- statement:
--   Every simple planar graph on at least three vertices has at most 3|V|−6 edges. This supplies the parent’s upper bound; the boundary case |V|=3 is included. A proof route is Euler’s formula applied across connected components, together with simplicity to bound face lengths.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_upper_bound_f81c96b6_b51d_4165_8b99_52e367cbc589
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
