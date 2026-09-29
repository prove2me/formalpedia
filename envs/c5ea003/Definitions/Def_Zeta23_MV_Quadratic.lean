-- Prove2me | Definitions.Def_Zeta23_MV_Quadratic
-- name    : Zeta23_MV_Quadratic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:08:41.112625+00:00
-- url     : https://prove2.me/theorems/5aeb481f-35ea-40f8-b2ce-b11451954f22
-- title:
--   The quadratic form $U = \sum_{m\neq n} \delta_m^{3/2}\delta_n^{1/2}\, t_m t_n/(\lambda_m-\lambda_n)^2$ (MV step 1)
-- statement:
--   This bundle defines the quadratic form at the heart of step 1 of the project's proof of the Montgomery–Vaughan inequality. For a finite index type $\iota$, frequencies $\lambda_m$ (`freq`), weights $\delta_m$, and real coefficients $t_m$, `MV.Uform` is
--   $$U \;:=\; \sum_{m \neq n} \frac{\delta_m^{3/2}\, \delta_n^{1/2}\; t_m t_n}{(\lambda_m - \lambda_n)^2},$$
--   formalized as the double sum over $m$ and $n \neq m$ of $\delta_m \sqrt{\delta_m}\sqrt{\delta_n}\, t_m t_n / (\lambda_m - \lambda_n)^2$.
--
--   Role: the surrounding module proves the bound $U \le 73 \sum_n t_n^2$ for nonnegative $t$ (the shape of arXiv:2203.14950, Theorem 1.2) via Cauchy–Schwarz and the spacing lemmas of `Zeta23/MV/Spacing.lean`. This quadratic-form bound feeds the eigenvalue estimate of MV step 3 (`eigen_bound`), and through the spectral reduction of `Zeta23/MV/Duality.lean` produces the diagonal Montgomery–Vaughan inequality `MVDiag`, making the H-MV input of the prime-side argument a theorem rather than an assumption.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Quadratic.lean

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 1 — the quadratic-form bound `U ≤ 73 V` (arXiv:2203.14950 Thm 1.2 shape)

`U := Σ_{m≠n} δ_m^{3/2} δ_n^{1/2} t_m t_n/(freq m − freq n)²  ≤  73 Σ t_n² ` for nonneg `t`:
Cauchy–Schwarz `U² ≤ V·W`; `W = S + T` (diagonal/off-diagonal of the expanded square);
`S ≤ 27V` (σ=4 spacing); `T ≤ 72U` (two-point lemma); the quadratic inequality gives `U ≤ 73V`.
-/

noncomputable section
open Real Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}

/-- The quadratic form `U = Σ_{m≠n} δ_m^{3/2} δ_n^{1/2} t_m t_n/(freq m − freq n)²`. -/
def Uform (freq δ : ι → ℝ) (t : ι → ℝ) : ℝ :=
  ∑ m, ∑ n ∈ Finset.univ.erase m,
    δ m * Real.sqrt (δ m) * Real.sqrt (δ n) * t m * t n / (freq m - freq n) ^ 2




end MV
end Zeta23


