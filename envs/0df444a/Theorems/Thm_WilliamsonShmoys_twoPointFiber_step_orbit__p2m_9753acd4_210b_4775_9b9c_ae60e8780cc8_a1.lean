-- Prove2me | Theorems.Thm_WilliamsonShmoys_twoPointFiber_step_orbit__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a1
-- name    : WilliamsonShmoys.twoPointFiber_step_orbit__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:13:06.766141+00:00
-- url     : https://prove2.me/theorems/cb23ac8c-db06-4d11-a240-e4b2c6ec42eb
-- title:
--   A fixed-point-free fiber-preserving step reaches every two-point fiber
-- statement:
--   For a finite type partitioned into fibers of size two, any step that stays in each fiber and has no fixed points reaches either point of a fiber from the other by iteration.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.twoPointFiber_step_orbit__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a1
    {X V : Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]
    (tail : X → V)
    (step : X → X)
    (hPres : ∀ x, tail (step x) = tail x)
    (hNoFix : ∀ x, step x ≠ x)
    (hCard : ∀ v, Fintype.card {x : X // tail x = v} = 2) :
    ∀ x y, tail x = tail y → ∃ k : Nat, step^[k] x = y := by sorry
