-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_hereditary_property_maximal_extension
-- name    : WilliamsonShmoys.finite_hereditary_property_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:48:14.433663+00:00
-- url     : https://prove2.me/theorems/477730ea-3211-4529-933d-9160c4ab552d
-- title:
--   Finite maximal extension for hereditary graph properties
-- statement:
--   For a finite vertex type, every graph satisfying a subgraph-hereditary property is contained in a graph maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.finite_hereditary_property_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hhered : ∀ G H : SimpleGraph V, H ≤ G → P G → P H)
    (R : SimpleGraph V)
    (hR : P R) :
    ∃ S : SimpleGraph V,
      R ≤ S ∧ P S ∧
      ∀ T : SimpleGraph V, S ≤ T → P T → T = S := by sorry
