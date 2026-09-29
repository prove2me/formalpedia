-- Prove2me | Theorems.Thm_Zeta23_Tail_tail_count_sum_le
-- name    : Zeta23.Tail.tail_count_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:45:31.283262+00:00
-- url     : https://prove2.me/theorems/0b909caf-1c8c-4928-aa2f-b7320c814f34
-- title:
--   Zero-count sum: $\sum_{\gamma \notin I'} m_\rho\, \mathrm{dist}(\gamma_\rho, I)^{-3} \le 4A_0\log(4T)/T$
-- statement:
--   **Setup.** Let $\gamma : \iota \to \mathbb{R}$ be an abstract family of zero ordinates with multiplicities $m : \iota \to \mathbb{N}$ satisfying `LocalCount γ m A₀`: $A_0 \ge 1$, and every finite subfamily lying in a unit window $(t, t+1]$ has total multiplicity at most $A_0\log(|t|+3)$. Let $T \ge T_0 := 300$. A zero is in the *tail* (`InTail T γ`) when its ordinate lies outside the enlarged window $I' = (T - \sqrt T,\, 2T + \sqrt T]$, i.e. $\gamma \le T - \sqrt T$ or $\gamma > 2T + \sqrt T$; and `distI T γ` $= \max(0, \max(T-\gamma, \gamma-2T))$ is the distance from $\gamma$ to $I = [T, 2T]$ (so $\mathrm{distI} \ge D_0 = \sqrt T$ for tail zeros).
--
--   **Statement.** For every finite set $s$ of tail zeros,
--   $$\sum_{\rho \in s} m_\rho\cdot \bigl(\mathrm{distI}\,T\,\gamma_\rho\bigr)^{-3} \;\le\; \frac{4\,A_0\,\log(4T)}{T},$$
--   where the denominator is $T = D_0^2$. Stated for arbitrary finite subfamilies so no summability of the full family is presupposed; the proof splits into the two sides of $I$ (`one_side_sum_le`) and finishes with the numeric estimate `two_sides_numeric`. This includes the zeros with $\gamma \le 0$, which have distance $\ge T$.
--
--   **Role.** This is the zero-count half of the proof of Proposition [prop:tail] in `Zeta23.Tail.Count`: multiplied by the per-zero bound $\|u_\rho\|_2^2 \le K^2 L\,\mathrm{dist}^{-3}$ it gives `TailHyp.partial_sum_le`, hence $\|\tilde E\| \le \theta_0$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Count.lean#L292-L389, docstring tag [prop:tail]

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Zeta23_Tail_Basic

open Finset Real
open Zeta23
open Tail

theorem Zeta23.Tail.tail_count_sum_le {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T : ℝ}
    (hN : LocalCount γ m A₀) (hT : T₀ ≤ T) (s : Finset ι) (hs : ∀ ρ ∈ s, InTail T (γ ρ)) :
    ∑ ρ ∈ s, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ ≤ 4 * A₀ * Real.log (4 * T) / T := by sorry
