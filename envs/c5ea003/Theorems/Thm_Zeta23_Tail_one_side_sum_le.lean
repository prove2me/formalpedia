-- Prove2me | Theorems.Thm_Zeta23_Tail_one_side_sum_le
-- name    : Zeta23.Tail.one_side_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:45:15.637951+00:00
-- url     : https://prove2.me/theorems/342d394a-0f27-49b3-8acd-754ced983877
-- title:
--   One-sided tail sum: $\sum m_\rho\, x_\rho^{-3}$ bounded via unit-window grouping
-- statement:
--   **Setup.** An abstract one-sided version of the tail count. Let $s$ be a finite index set, $x : \iota \to \mathbb{R}$ the (signed) distances of zeros beyond one endpoint of the window $I$, $m : \iota \to \mathbb{N}$ their multiplicities, and $\mathrm{key} : \iota \to \mathbb{N}$ an integer grouping key. Assume constants $A_0 \ge 0$, $B \ge 1$, $D_0 \ge 2$, and: every $\rho \in s$ has $x_\rho \ge D_0$ (it lies at distance at least $D_0$ beyond the endpoint); the key brackets the distance, $\mathrm{key}(\rho) \le x_\rho \le \mathrm{key}(\rho) + 1$ (unit windows); and each group is controlled by the local zero count, $\sum_{\rho \in s,\ \mathrm{key}(\rho) = j} m_\rho \le A_0 \log(B + j)$ for every $j \in \mathbb{N}$.
--
--   **Statement.** Under these hypotheses,
--   $$\sum_{\rho \in s} \frac{m_\rho}{x_\rho^{3}} \;\le\; A_0\left[\left(\frac{2}{D_0^{3}} + \frac{1}{2D_0^{2}}\right)\log B \;+\; \frac{1}{B}\left(\frac{2}{D_0^{2}} + \frac{1}{D_0}\right)\right].$$
--   This groups the tail zeros on one side of $I$ into unit windows indexed by $j$, bounds each window by $A_0\log(B+j)$, and sums the window weights via `sum_window_weights_le`.
--
--   **Role.** Applied to each of the two sides of the window (with $D_0 = \sqrt T$ and $B = 2T + 4$) and combined with the numeric estimate `two_sides_numeric`, it yields `tail_count_sum_le`, the zero-count sum $\sum m_\rho\,\mathrm{dist}(\gamma_\rho, I)^{-3} \le 4A_0\log(4T)/T$ of Proposition [prop:tail] in the `Zeta23.Tail.Count` module.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Count.lean#L198-L241

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

theorem Zeta23.Tail.one_side_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (m : ι → ℕ) (key : ι → ℕ)
    {A₀ B D₀ : ℝ} (hA₀ : 0 ≤ A₀) (hB : 1 ≤ B) (hD₀ : 2 ≤ D₀)
    (hx : ∀ ρ ∈ s, D₀ ≤ x ρ) (hkey_le : ∀ ρ ∈ s, (key ρ : ℝ) ≤ x ρ)
    (hkey_ge : ∀ ρ ∈ s, x ρ ≤ key ρ + 1)
    (hcount : ∀ j : ℕ, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) ≤ A₀ * Real.log (B + j)) :
    ∑ ρ ∈ s, (m ρ : ℝ) * ((x ρ) ^ 3)⁻¹
      ≤ A₀ * ((2 * (D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B
          + (2 * (D₀ ^ 2)⁻¹ + D₀⁻¹) / B) := by sorry
