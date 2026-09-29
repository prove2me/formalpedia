-- Prove2me | Theorems.Thm_Zeta23_Tail_grid_sum_le
-- name    : Zeta23.Tail.grid_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:44:49.61698+00:00
-- url     : https://prove2.me/theorems/ad4f7b49-d5b9-4285-bcaa-dde1bb8cfad8
-- title:
--   Grid estimate: $\sum_{k<d} |\gamma - \tau_k|^{-4} \le L\cdot \mathrm{dist}(\gamma, I)^{-3}$
-- statement:
--   **Setup.** Fix reals $T > 0$, $L \ge 2$ and a natural number $d$ with $d\cdot h \le T$, where $h := 2\pi/L$ is the grid step. The grid points are $\tau_k := T + k h$ for $k = 0, \dots, d-1$; in the application $L = \lambda\ell(T)$ is the logarithmic length and $d = \lfloor LT/2\pi\rfloor$, so the $\tau_k$ fill the window $I = [T, 2T]$. For an ordinate $\gamma \in \mathbb{R}$, `distI T γ` $:= \max\bigl(0,\ \max(T - \gamma,\ \gamma - 2T)\bigr)$ is its distance to the interval $I = [T, 2T]$; assume $D := \mathrm{distI}\,T\,\gamma \ge 1$, i.e. $\gamma$ lies at distance at least $1$ outside the window.
--
--   **Statement.** Under these hypotheses,
--   $$\sum_{k=0}^{d-1} \frac{1}{|\gamma - (T + k\cdot 2\pi/L)|^{4}} \;\le\; \frac{L}{(\mathrm{distI}\,T\,\gamma)^{3}}.$$
--   The proof telescopes the sum (`sum_inv_pow_four_le_telescope`) and absorbs the constants using $D \ge 1$, $L \ge 2$ (`grid_const_bound`).
--
--   **Role.** This is the Grid step in the proof of Proposition [prop:tail]: combined with the entrywise decay $\|u_\rho(k)\| \le K|\gamma_\rho - \tau_k|^{-2}$ it gives `norm_sq_uvec_le`, the bound $\|u_\rho\|_2^2 \le K^2 L\,\mathrm{dist}(\gamma, I)^{-3}$ for each tail zero $\rho$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Grid.lean#L93-L140, docstring tag [prop:tail]

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_Zeta23_Tail_Basic

open Finset Real
open Zeta23
open Tail

theorem Zeta23.Tail.grid_sum_le {T L γ : ℝ} {d : ℕ} (hL : 2 ≤ L) (hT : 0 < T)
    (hd : (d : ℝ) * (2 * π / L) ≤ T) (hD : 1 ≤ distI T γ) :
    ∑ k ∈ range d, (|γ - (T + k * (2 * π / L))| ^ 4)⁻¹ ≤ L * ((distI T γ) ^ 3)⁻¹ := by sorry
