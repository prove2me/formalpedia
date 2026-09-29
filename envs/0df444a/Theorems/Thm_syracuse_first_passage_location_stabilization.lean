-- Prove2me | Theorems.Thm_syracuse_first_passage_location_stabilization
-- name    : syracuse_first_passage_location_stabilization
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-28T15:09:45.819642+00:00
-- url     : https://prove2.me/theorems/ab866d4c-b976-4dfe-a474-a5d040d15461
-- title:
--   Tao Proposition 1.11, estimate (1.20): first-passage location stabilization
-- statement:
--   In Tao's 'Almost all orbits of the Collatz map attain almost bounded values' (Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7), Proposition 1.11 gives two estimates for the Syracuse first-passage location Pass_x under the log-uniform probability measure N_y on odd integers in [y, y^α] with α = 1.001. Estimate (1.20): there are absolute positive constants C₂, c₂ and a threshold x₀ ≥ 2 such that for every x ≥ x₀ with nonempty windows, the total-variation distance between the distributions of the first-passage location Pass_x(N_{x^α}) and Pass_x(N_{x^(α²)}) — the supremum over all events of the difference of their N_y-probabilities — is at most C₂ * (log x)^(-c₂). This is the hard input to Theorem 3.1: Tao deduces it from Proposition 1.14 (fine-scale mixing of Syracuse offsets, Sections 6-9: Fourier analysis on 3-adics and a renewal-process approximation). Together with estimate (1.19), it drives the telescoping iteration in Section 3 that yields the uniform logarithmic tail bound for Syracuse orbit minima, the keystone of the tao-collatz mission.

import Mathlib
import Definitions.Def_syracuseOrbitMin

noncomputable section


attribute [instance] Classical.propDecidable

namespace Tao120

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

/-- First passage location: the orbit's first entry into `(-∞, x]`
    (Tao 2022 §1.3, `Pass_x`); junk value `1` if passage never occurs. -/
def firstPassLoc (x : ℝ) (n : ℕ) : ℕ :=
  ((firstPassTime x n).map fun k => syracuseStep^[k] n).getD 1

/-- Total `1 / n` weight of a window. -/
def winWeight (y : ℝ) : ℝ :=
  Finset.sum (logWindow y) fun n => (1 / (n : ℝ))

/-- Weighted (log-uniform) probability of an event over a window. -/
def winProb (y : ℝ) (p : ℕ → Prop) : ℝ :=
  (Finset.sum ((logWindow y).filter p) fun n => (1 / (n : ℝ))) / winWeight y

end Tao120

theorem syracuse_first_passage_location_stabilization :
    ∃ C₂ c₂ x₀ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        (Tao120.logWindow (x ^ Tao120.taoAlpha)).Nonempty →
        (Tao120.logWindow ((x ^ Tao120.taoAlpha) ^ Tao120.taoAlpha)).Nonempty →
        ∀ p : ℕ → Prop,
          |Tao120.winProb (x ^ Tao120.taoAlpha)
              (fun n => p (Tao120.firstPassLoc x n)) -
            Tao120.winProb ((x ^ Tao120.taoAlpha) ^ Tao120.taoAlpha)
              (fun n => p (Tao120.firstPassLoc x n))| ≤
            C₂ * (Real.log x) ^ (-c₂) := by sorry
