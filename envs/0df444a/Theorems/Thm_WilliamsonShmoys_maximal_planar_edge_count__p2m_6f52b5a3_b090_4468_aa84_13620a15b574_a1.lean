-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:33:27.535145+00:00
-- url     : https://prove2.me/theorems/ccb6a6bc-2d03-4d79-9277-48639c2dde63
-- title:
--   A maximal drawable graph has the planar triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph with at least three vertices has exactly 3|V| − 6 edges. The proof route is the standard one: maximality forces a connected triangulation (any face with more than three boundary vertices permits a noncrossing diagonal); Euler's formula gives |V| − |E| + |F| = 2, and counting face-edge incidences gives 3|F| = 2|E|, yielding |E| = 3|V| − 6. The hypothesis |V| ≥ 3 is essential to this formula and handles the smallest allowed case, the triangle. This child isolates the main topological counting obligation; the parent then combines its count with the supergraph from the first child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) (hmax : ∀ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) (hCard : 3 ≤ Fintype.card V) : N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
