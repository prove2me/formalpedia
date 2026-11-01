-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_tight_edges__p2m_b575e78e_3e28_4118_93fc_258c931bc299_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_tight_edges__p2m_b575e78e_3e28_4118_93fc_258c931bc299_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:31.711027+00:00
-- url     : https://prove2.me/theorems/a41fea2b-c624-4d83-8365-0ca98a452bee
-- title:
--   A planar graph extends to a tight planar supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges. This isolates the augmentation and planar edge-count work needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_tight_edges__p2m_b575e78e_3e28_4118_93fc_258c931bc299_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ P : SimpleGraph V,
      (∀ {u v : V}, N.Adj u v → P.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (letI : DecidableRel P.Adj := Classical.decRel P.Adj
       P.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
