-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_eq_of_le_of_adjPairCard_le__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
-- name    : WilliamsonShmoys.simpleGraph_eq_of_le_of_adjPairCard_le__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:18:06.529743+00:00
-- url     : https://prove2.me/theorems/5153a095-1513-4dc2-8878-9b1b64469e65
-- title:
--   Graph equality from inclusion and adjacent-pair count
-- statement:
--   For a finite vertex type, if `H` is a subgraph of `K` and `K` has no more ordered adjacent pairs than `H`, then the graphs are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_eq_of_le_of_adjPairCard_le__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hcard : Nat.card {p : V × V // K.Adj p.1 p.2} ≤
      Nat.card {p : V × V // H.Adj p.1 p.2}) :
    K = H := by sorry
