-- Prove2me | Theorems.Thm_WilliamsonShmoys_iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
-- name    : WilliamsonShmoys.iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:22:09.233792+00:00
-- url     : https://prove2.me/theorems/a49e8573-7163-46f3-bc6a-b6dc614057e1
-- title:
--   Iterate drawable bridges to connect a graph
-- statement:
--   For a finite vertex type of cardinality at least three, any graph satisfying a property can be extended to a connected graph with the same property if each disconnected graph satisfying it admits a property-preserving edge addition between distinct unreachable vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : P K)
    (hStep : ∀ (G : SimpleGraph V), P G → 3 ≤ Fintype.card V → ¬ G.Connected →
      ∃ u v : V,
        u ≠ v ∧ ¬ G.Reachable u v ∧ ¬ G.Adj u v ∧
        P (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)))
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ P H := by sorry
