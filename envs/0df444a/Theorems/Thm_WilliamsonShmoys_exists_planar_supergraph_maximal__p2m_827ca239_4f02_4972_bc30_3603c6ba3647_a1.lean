-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal__p2m_827ca239_4f02_4972_bc30_3603c6ba3647_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_maximal__p2m_827ca239_4f02_4972_bc30_3603c6ba3647_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:35.698212+00:00
-- url     : https://prove2.me/theorems/f3fecaac-4a9c-413e-8409-541c055f1b8c
-- title:
--   Finite graph extension to a maximal predicate-satisfying supergraph
-- statement:
--   For any property of graphs on a fixed finite ordered vertex type, if L satisfies the property, then L has a property-satisfying supergraph that is maximal among property-satisfying graphs under adjacency inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_maximal__p2m_827ca239_4f02_4972_bc30_3603c6ba3647_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) [DecidableRel L.Adj] (P : SimpleGraph V → Prop) (hL : P L) : ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj), (letI : DecidableRel H.Adj := dH; L.edgeFinset ⊆ H.edgeFinset ∧ P H ∧ (∀ K : SimpleGraph V, (∀ u v, H.Adj u v → K.Adj u v) → P K → ∀ u v, K.Adj u v → H.Adj u v)) := by sorry
