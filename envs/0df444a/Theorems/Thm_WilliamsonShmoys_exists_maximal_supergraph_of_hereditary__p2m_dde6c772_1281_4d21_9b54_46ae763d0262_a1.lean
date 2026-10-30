-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_hereditary__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_hereditary__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:53.595529+00:00
-- url     : https://prove2.me/theorems/79adc0d7-3a11-418b-99ea-c41dca74eed5
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   On a finite vertex type, every graph satisfying a downward-closed property is contained in a supergraph satisfying that property which has no strictly larger supergraph satisfying it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_hereditary__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1 {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V -> Prop) (hmono : forall {G H : SimpleGraph V}, LE.le G H -> P H -> P G) (G : SimpleGraph V) (hG : P G) : Exists fun W : SimpleGraph V => And (LE.le G W) (And (P W) (forall X : SimpleGraph V, LE.le W X -> P X -> X = W)) := by sorry
