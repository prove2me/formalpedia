-- Prove2me | Theorems.Thm_syracuse_cycle_period_bounds_at_seven_floors
-- name    : syracuse_cycle_period_bounds_at_seven_floors
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:26:04.234336+00:00
-- url     : https://prove2.me/theorems/24980bcb-fe3b-55a0-8937-8381613d5873
-- title:
--   Syracuse period bounds at seven verified orbit floors
-- statement:
--   For a positive-period Syracuse orbit at a positive floor B, the total dyadic valuation K exceeds 16785921/10590737 times its return period. At each of the seven listed floors, a certified rational interval for K/p gives the stated integer lower bound on p. The hypotheses apply to all states on the orbit.
-- source:
--   Combines exact Syracuse step products, rigorous logarithm bounds and adjacent Farey endpoints. The cycle power-gap lemma is imported from the Collatz mission.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem syracuse_cycle_period_bounds_at_seven_floors (m p B : ℕ) (hp : 0 < p) (hB : 0 < B)
    (hf : ∀ i : ℕ, B ≤ syracuseStep^[i] m) (hcyc : syracuseStep^[p] m = m) :
    let K := (Finset.range p).sum fun i => (3*syracuseStep^[i] m+1).factorization 2
    16785921*p < 10590737*K ∧
    (8000000000 ≤ B → 190537 ≤ p) ∧
    (1000000000000 ≤ B → 10781274 ≤ p) ∧
    (1000000000000000 ≤ B → 64497107 ≤ p) ∧
    (1000000000000000000 ≤ B → 397573379 ≤ p) ∧
    (1000000000000000000000000 ≤ B → 2396860564955 ≤ p) ∧
    (1000000000000000000000000000000 ≤ B → 2849242656677982 ≤ p) ∧
    (340282366920938463463374607431768211456 ≤ B → 27444133206411171953 ≤ p) := by sorry
