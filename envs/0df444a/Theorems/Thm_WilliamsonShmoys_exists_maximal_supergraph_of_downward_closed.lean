-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_downward_closed
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:59:12.252263+00:00
-- url     : https://prove2.me/theorems/aa17950e-76a3-48e4-8802-d0b96ae16c12
-- title:
--   Finite maximal supergraph for a downward-closed property
-- statement:
--   For a finite vertex type, every graph satisfying a downward-closed property is contained in an inclusion-maximal graph satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G)
    (G : SimpleGraph V) (hG : P G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ P L ∧
      ∀ K : SimpleGraph V, L ≤ K → P K → K ≤ L := by sorry
