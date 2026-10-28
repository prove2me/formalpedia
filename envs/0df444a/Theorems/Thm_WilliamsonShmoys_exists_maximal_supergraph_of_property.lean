-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_property
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:21:33.034983+00:00
-- url     : https://prove2.me/theorems/27444880-0064-45c3-a4cc-31828db7c5ab
-- title:
--   Maximal finite graph satisfying a property
-- statement:
--   For a graph on a finite vertex type, every property satisfied by M has a supergraph satisfying that property that admits no proper supergraph with the property. The boundary case of zero vertices or zero edges is included: maximizing edge count still applies.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_property
    {V : Type} [Fintype V]
    (M : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by sorry
