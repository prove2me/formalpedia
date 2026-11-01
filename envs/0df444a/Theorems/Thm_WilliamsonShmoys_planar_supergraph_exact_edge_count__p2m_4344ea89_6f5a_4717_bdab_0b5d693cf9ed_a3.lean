-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count__p2m_4344ea89_6f5a_4717_bdab_0b5d693cf9ed_a3
-- name    : WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_4344ea89_6f5a_4717_bdab_0b5d693cf9ed_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:59:15.64865+00:00
-- url     : https://prove2.me/theorems/ffd766b2-d86f-4f00-bea0-c76fad60558a
-- title:
--   Planar supergraph with exact edge count
-- statement:
--   Every finite planar simple graph on at least three vertices is contained in a planar simple graph on the same vertex type with exactly `3|V| - 6` edges. The child carries the extension, connectivity, triangulation, and Euler-formula argument; its `|V| ≥ 3` condition preserves the triangle boundary case. A proof route is to choose an edge-maximal planar supergraph among the finite simple graphs on `V`, establish connectedness and triangular faces for its embedding, and count using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_4344ea89_6f5a_4717_bdab_0b5d693cf9ed_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
