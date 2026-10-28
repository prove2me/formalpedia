-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_of_downward_closed_property
-- name    : WilliamsonShmoys.exists_maximal_simpleGraph_of_downward_closed_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:24:40.420797+00:00
-- url     : https://prove2.me/theorems/6c21620c-b94f-4052-969b-a241dcdecab3
-- title:
--   Finite maximal extension for downward-closed graph properties
-- statement:
--   For a finite vertex type, every graph satisfying a downward-closed property is contained in a graph maximal among its supergraphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_simpleGraph_of_downward_closed_property
    {V : Type} [Fintype V] [DecidableEq V]
    (Good : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → Good B → Good A)
    (G : SimpleGraph V)
    (hG : Good G) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ Good P ∧
        ∀ Q : SimpleGraph V, P ≤ Q → Good Q → Q ≤ P := by sorry
