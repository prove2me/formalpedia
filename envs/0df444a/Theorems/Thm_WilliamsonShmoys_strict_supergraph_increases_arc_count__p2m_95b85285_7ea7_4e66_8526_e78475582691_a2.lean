-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_supergraph_increases_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
-- name    : WilliamsonShmoys.strict_supergraph_increases_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:00:24.505822+00:00
-- url     : https://prove2.me/theorems/f888f3ce-f278-4984-acba-ae24eb9a1757
-- title:
--   Strict graph inclusion increases adjacency count
-- statement:
--   If `K ≤ H` but `H ≤ K` fails, some ordered pair is adjacent in `H` and not in `K`. The adjacency subtype for `K` therefore embeds properly into the finite adjacency subtype for `H`, so its `Nat.card` is strictly smaller. This supplies the parent’s contradiction to maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.strict_supergraph_increases_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
    {V : Type} [Fintype V] [LinearOrder V] (K H : SimpleGraph V)
    (hKH : K ≤ H) (hnot : ¬ H ≤ K) :
    Nat.card {p : V × V // K.Adj p.1 p.2} <
      Nat.card {p : V × V // H.Adj p.1 p.2} := by sorry
