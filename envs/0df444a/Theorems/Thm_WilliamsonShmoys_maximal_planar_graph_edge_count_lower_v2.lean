-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_v2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_lower_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:08:56.39886+00:00
-- url     : https://prove2.me/theorems/f7209867-b56d-4aea-b839-fc45f86de26d
-- title:
--   A maximal drawable graph has at least 3n minus 6 edges
-- statement:
--   A drawable graph that has no proper drawable supergraph on the same vertex set has at least 3|V|−6 edges, provided |V|≥3. This removes the planar edge-count argument from the parent while retaining its exact size and maximality hypotheses. A proof route is to derive connectedness and triangular faces from maximality, count face-edge incidences, and combine that count with Euler’s formula. The boundary case |V|=3 is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_lower_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → N ≤ K → K = N)
    (hCard : 3 <= Fintype.card V) :
    3 * (Fintype.card V : Int) - 6 <= (N.edgeSet.ncard : Int) := by sorry
