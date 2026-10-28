-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_property_f877e9d9
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_finite_property_f877e9d9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:58:28.506844+00:00
-- url     : https://prove2.me/theorems/26d265fb-a5ff-4ea6-83c2-8ae374eed674
-- title:
--   A finite graph property has a maximal supergraph
-- statement:
--   For any property of simple graphs on a finite vertex type, every graph satisfying that property has a supergraph with the property that is maximal among property-satisfying supergraphs and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_for_finite_property_f877e9d9
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      P H ∧
      (∀ J : SimpleGraph V, H ≤ J → P J → J = H) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
