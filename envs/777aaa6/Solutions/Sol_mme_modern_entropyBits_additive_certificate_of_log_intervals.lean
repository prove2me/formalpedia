-- Prove2me | solution 1 for mme_modern_entropyBits_additive_certificate_of_log_intervals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T15:11:30.551144+00:00
-- url     : https://prove2.me/submissions/493c224e-d4e2-4f5c-828c-0dc0056e2943

import Theorems.Thm_mme_modern_entropyBits_additive_certificate

open BigOperators

universe u v w x

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {D : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    [Fintype D] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : D → X) (coordY : D → Y) (coordZ : D → Z)
    (rho y : D → ℝ)
    (lambdaZero : ℝ)
    (lambdaX : X → ℝ) (lambdaY : Y → ℝ) (lambdaZ : Z → ℝ)
    (lower upper : D → ℝ) (ε : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hy : ∀ a, 0 < y a)
    (hrhoSum : ∑ a, rho a = 1) (hySum : ∑ a, y a = 1)
    (hmargX : ∀ i, mme_modern_marginal coordX rho i =
      mme_modern_marginal coordX y i)
    (hmargY : ∀ i, mme_modern_marginal coordY rho i =
      mme_modern_marginal coordY y i)
    (hmargZ : ∀ i, mme_modern_marginal coordZ rho i =
      mme_modern_marginal coordZ y i)
    (hε : 0 ≤ ε)
    (hlogLower : ∀ a, lower a ≤ Real.log (y a) / Real.log 2)
    (hlogUpper : ∀ a, Real.log (y a) / Real.log 2 ≤ upper a)
    (hintervalLower : ∀ a,
      lambdaZero + lambdaX (coordX a) + lambdaY (coordY a) +
          lambdaZ (coordZ a) - ε ≤ lower a)
    (hintervalUpper : ∀ a,
      upper a ≤ lambdaZero + lambdaX (coordX a) +
          lambdaY (coordY a) + lambdaZ (coordZ a) + ε) :
    mme_modern_entropyBits rho ≤ mme_modern_entropyBits y + 2 * ε := by
  apply mme_modern_entropyBits_additive_certificate
    coordX coordY coordZ rho y lambdaZero lambdaX lambdaY lambdaZ ε
    hrho hy hrhoSum hySum hmargX hmargY hmargZ hε
  intro a
  rw [abs_le]
  constructor
  · linarith [hlogLower a, hintervalLower a]
  · linarith [hlogUpper a, hintervalUpper a]
