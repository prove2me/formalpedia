-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_property_has_maximal_extension__p2m_4274c3cc_8877_4dcd_9fb0_968a87bc56a7_a1
-- name    : WilliamsonShmoys.finite_graph_property_has_maximal_extension__p2m_4274c3cc_8877_4dcd_9fb0_968a87bc56a7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:04.871126+00:00
-- url     : https://prove2.me/theorems/9e293885-497b-4f37-a790-b8166f742204
-- title:
--   Maximal extension for a property on finite graphs
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has an extension satisfying it that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_property_has_maximal_extension__p2m_4274c3cc_8877_4dcd_9fb0_968a87bc56a7_a1 {V : Type} [Fintype V] (P : SimpleGraph V -> Prop) (K : SimpleGraph V) (hK : P K) : Exists fun L : SimpleGraph V => And (LE.le K L) (And (P L) (forall M : SimpleGraph V, LE.le L M -> P M -> M = L)) := by sorry
