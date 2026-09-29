-- Prove2me | Theorems.Thm_syracuse_first_passage_finite_tail_bound
-- name    : syracuse_first_passage_finite_tail_bound
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-28T15:09:30.086185+00:00
-- url     : https://prove2.me/theorems/b179e2a6-29fd-4151-8b97-35fd2e1bb5a1
-- title:
--   Tao Proposition 1.11, estimate (1.19): first-passage finiteness tail bound
-- statement:
--   In Tao's 'Almost all orbits of the Collatz map attain almost bounded values' (Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7), Proposition 1.11 gives two estimates for the Syracuse first-passage time T_x under the log-uniform probability measure N_y on odd integers in [y, y^α] with α = 1.001. Estimate (1.19): there are absolute positive constants C₁, c₁ and a threshold x₀ ≥ 2 such that for every x ≥ x₀ and both scales y in {x^α, x^(α²)} with nonempty window, the N_y-probability that the first passage time T_x is infinite (the Syracuse orbit never drops to or below x) is at most C₁ * x^(-c₁). Tao calls this estimate 'easy to establish'; it is proved in Section 5 from Proposition 1.9 by elementary residue-class counting. It is the finite-time input to the proof of Theorem 3.1 (the uniform logarithmic tail bound for Syracuse orbit minima), the keystone of the tao-collatz mission.

import Mathlib
import Definitions.Def_syracuseOrbitMin

noncomputable section


attribute [instance] Classical.propDecidable

namespace Tao119

/-- Tao 2022, (1.18): the constant `α = 1.001`. -/
def taoAlpha : ℝ := 1.001

/-- Log-uniform sample window: odd `n` with `y ≤ n ≤ y ^ α`
    (support of Tao's `ℕ_y = Log(2ℕ+1 ∩ [y, y^α])`, Proposition 1.11). -/
def logWindow (y : ℝ) : Finset ℕ :=
  Finset.filter (fun n => Odd n ∧ y ≤ (n : ℝ) ∧ (n : ℝ) ≤ y ^ taoAlpha)
    (Finset.Icc 1 ⌈y ^ taoAlpha⌉₊)

/-- First passage time below `x`: least `k` with `syracuseStep^[k] n ≤ x`
    (Tao 2022 §1.3, `T_x`); `none` if the orbit never drops to or below `x`. -/
def firstPassTime (x : ℝ) (n : ℕ) : Option ℕ :=
  if h : ∃ k : ℕ, ((syracuseStep^[k] n : ℕ) : ℝ) ≤ x then
    some (Nat.find h)
  else none

/-- Total `1 / n` weight of a window. -/
def winWeight (y : ℝ) : ℝ :=
  Finset.sum (logWindow y) fun n => (1 / (n : ℝ))

/-- Weighted (log-uniform) probability of an event over a window. -/
def winProb (y : ℝ) (p : ℕ → Prop) : ℝ :=
  (Finset.sum ((logWindow y).filter p) fun n => (1 / (n : ℝ))) / winWeight y

end Tao119

theorem syracuse_first_passage_finite_tail_bound :
    ∃ C₁ c₁ x₀ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ y ∈ ({x ^ Tao119.taoAlpha, (x ^ Tao119.taoAlpha) ^ Tao119.taoAlpha} : Finset ℝ),
          (Tao119.logWindow y).Nonempty →
          Tao119.winProb y (fun n => (Tao119.firstPassTime x n).isNone) ≤
            C₁ * x ^ (-c₁) := by sorry
