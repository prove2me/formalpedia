-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_three_vertices
-- name    : WilliamsonShmoys.planar_connected_supergraph_three_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:54:28.604728+00:00
-- url     : https://prove2.me/theorems/6f353edf-aeca-493d-ac2f-9cd7c9a7c158
-- title:
--   Connected planar supergraph on at least three vertices
-- statement:
--   A graph on at least three vertices with a crossing-free drawing has a connected planar supergraph on the same vertices. The edge inclusion preserves every original edge and implies the required edge-count inequality. A proof can join components through shared faces and iterate; it must handle nested components and formalize the new arcs against the given drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_supergraph_three_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.Connected ∧
      P ≤ Q ∧
      P.edgeSet.ncard ≤ Q.edgeSet.ncard := by
  sorry
