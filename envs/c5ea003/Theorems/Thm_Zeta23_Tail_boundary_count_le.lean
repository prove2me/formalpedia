-- Prove2me | Theorems.Thm_Zeta23_Tail_boundary_count_le
-- name    : Zeta23.Tail.boundary_count_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:44:27.062921+00:00
-- url     : https://prove2.me/theorems/c50fd869-dde1-4877-99b0-9462a185a31a
-- title:
--   Boundary count: $N(I' \setminus I) \le 3A_0\sqrt{T}\log(4T)$
-- statement:
--   **Setup.** Let $\gamma : \iota \to \mathbb{R}$ be an abstract family of zero ordinates with multiplicities $m : \iota \to \mathbb{N}$, satisfying the local-count hypothesis `LocalCount γ m A₀`: $A_0 \ge 1$ and for every real $t$ and every finite subfamily contained in the unit window $(t, t+1]$, the multiplicities sum to at most $A_0\log(|t|+3)$ (the classical bound $N(t+1)-N(t) \ll \log t$ in two-sided unit-window form). Let $T \ge T_0 := 300$. The boundary region $I'\setminus I$ consists of the two strips $(T-\sqrt T,\, T] \cup (2T,\, 2T+\sqrt T]$ between the window $I = [T, 2T]$ and the enlarged window $I' = (T-\sqrt T,\, 2T+\sqrt T]$ (recall $D_0 := \sqrt T$).
--
--   **Statement.** For every finite set $s$ of indices whose ordinates all lie in the boundary region, i.e. $\gamma_\rho \in (T-\sqrt T, T] \cup (2T, 2T+\sqrt T]$ for all $\rho \in s$,
--   $$\sum_{\rho \in s} m_\rho \;\le\; 3\, A_0\, \sqrt{T}\, \log(4T).$$
--   Combined with $\log(4T) \le 2\ell(T)$ for $T \ge T_0$ (`log_four_mul_le_two_mul_l`), this is the paper's "$N(I'\setminus I) \ll D_0\, l$ by $N(t+1)-N(t) \le A_0\log(t+3)$" used in [prop:zeroside] and [prop:zeroside-rank]. The count is stated for arbitrary finite subfamilies so no global summability is presupposed.
--
--   **Role.** It feeds `Zeta23.Tail.NII_le` in the `Zeta23.Tail.Count` module, which converts it into the eventual bound $N(I'\setminus I) \le C\sqrt T\,\ell(T)$ consumed by the zero-side rank estimates.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Count.lean#L405-L496, docstring tags [prop:zeroside], [prop:zeroside-rank]

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Zeta23_Tail_Basic

open Finset Real
open Zeta23
open Tail

theorem Zeta23.Tail.boundary_count_le {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T : ℝ}
    (hN : LocalCount γ m A₀) (hT : T₀ ≤ T) (s : Finset ι)
    (hs : ∀ ρ ∈ s, (T - Real.sqrt T < γ ρ ∧ γ ρ ≤ T)
      ∨ (2 * T < γ ρ ∧ γ ρ ≤ 2 * T + Real.sqrt T)) :
    ∑ ρ ∈ s, (m ρ : ℝ) ≤ 3 * A₀ * Real.sqrt T * Real.log (4 * T) := by sorry
