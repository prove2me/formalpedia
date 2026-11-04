-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
-- name    : WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:07.502517+00:00
-- url     : https://prove2.me/theorems/6aea0192-1a29-46e3-846e-b5510acd39b3
-- title:
--   Lower edge bound for an edge-maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset = L.edgeFinset) :
    3 * Fintype.card V - 6 <= L.edgeFinset.card := by
  sorry
