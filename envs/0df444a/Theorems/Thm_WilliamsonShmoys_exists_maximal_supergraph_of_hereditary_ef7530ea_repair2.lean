-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_hereditary_ef7530ea_repair2
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_hereditary_ef7530ea_repair2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:10:19.637933+00:00
-- url     : https://prove2.me/theorems/1fe2d738-db32-4fa1-b34c-f9db87050fba
-- title:
--   Finite hereditary graph properties admit maximal supergraphs
-- statement:
--   For an edge-hereditary property on graphs over a finite vertex type, every graph satisfying the property has a supergraph satisfying it that is maximal under edge inclusion. Choose an extension with the largest edge count; any proper extension would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_hereditary_ef7530ea_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hP : ∀ G H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) → P H → P G)
    (N : SimpleGraph V) (hN : P N) :
    ∃ M : SimpleGraph V,
      (∀ u v, N.Adj u v → M.Adj u v) ∧
      (P M ∧ ∀ M' : SimpleGraph V,
        (∀ u v, M.Adj u v → M'.Adj u v) → P M' →
        ∀ u v, M'.Adj u v → M.Adj u v) := by sorry
