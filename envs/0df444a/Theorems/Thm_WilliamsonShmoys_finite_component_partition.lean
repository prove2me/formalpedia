-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_component_partition
-- name    : WilliamsonShmoys.finite_component_partition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:33:20.095443+00:00
-- url     : https://prove2.me/theorems/662d7f1d-dc3e-48b9-bd43-f5f851d87c87
-- title:
--   Finite graph partition into connected components
-- statement:
--   Every finite simple graph has a finite family of nonempty vertex sets that partitions its vertices, puts the endpoints of every edge in one set, and induces a connected graph on each set. The empty graph uses the empty family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_component_partition
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) :
    ∃ C : Finset (Finset V),
      (∀ S ∈ C, S.Nonempty) ∧
      (∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S) ∧
      (∀ ⦃u v : V⦄, H.Adj u v → ∃ S ∈ C, u ∈ S ∧ v ∈ S) ∧
      (∀ S ∈ C, (H.induce (↑S : Set V)).Connected) := by sorry
