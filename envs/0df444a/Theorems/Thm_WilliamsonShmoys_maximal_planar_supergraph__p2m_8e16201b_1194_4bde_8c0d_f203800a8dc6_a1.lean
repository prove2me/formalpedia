-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:50.421517+00:00
-- url     : https://prove2.me/theorems/57a6043d-0c29-4d4d-8b4a-350055d97afc
-- title:
--   A maximal planar supergraph exists
-- statement:
--   Every finite drawn graph has a planar supergraph that contains its edges, has at least as many edges, and is maximal under planar supergraph inclusion. The finite search over simple graphs on V, maximizing edge count among planar supergraphs of K, is a direct proof route. This removes the parent’s finite maximality and edge-count bookkeeping; the parent still needs the topological strict-extension lemma to show this maximal graph is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun (H : SimpleGraph V) =>
      Exists fun (dH : DecidableRel H.Adj) =>
        And (K ≤ H)
          (And (WilliamsonShmoys.HasPlanarDrawingOn H)
            (And (Nat.le K.edgeFinset.card H.edgeFinset.card)
              (∀ (J : SimpleGraph V), ∀ (dJ : DecidableRel J.Adj),
                K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J →
                  H ≤ J → J = H))) := by
  sorry
