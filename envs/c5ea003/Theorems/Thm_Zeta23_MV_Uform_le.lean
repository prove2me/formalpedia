-- Prove2me | Theorems.Thm_Zeta23_MV_Uform_le
-- name    : Zeta23.MV.Uform_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:52:28.963713+00:00
-- url     : https://prove2.me/theorems/9566745f-0442-428b-a5ba-592c98df248e
-- title:
--   Quadratic-form bound (Step 1): $U \le 73 \sum_n t_n^2$
-- statement:
--   Let $\iota$ be a finite index type, $\mathrm{freq} \colon \iota \to \mathbb{R}$ a family of frequencies, and $\delta \colon \iota \to \mathbb{R}$ admissible weights, meaning: $\mathrm{freq}$ is injective, $\delta_r > 0$ for all $r$, and $\delta_r \le |\mathrm{freq}_r - \mathrm{freq}_s|$ for all $r \ne s$ (the shape of the hypotheses of the Montgomery–Vaughan inequality `Zeta23.MVHilbert`). For a real vector $t \colon \iota \to \mathbb{R}$ define the quadratic form
--
--   $$U(t) \;=\; \sum_{m} \sum_{n \ne m} \frac{\delta_m^{3/2}\, \delta_n^{1/2}\, t_m\, t_n}{(\mathrm{freq}_m - \mathrm{freq}_n)^2}$$
--
--   (`Uform`, written in Lean as $\delta_m \sqrt{\delta_m}\sqrt{\delta_n}\, t_m t_n/(\mathrm{freq}_m-\mathrm{freq}_n)^2$). Then for every entrywise nonnegative $t$,
--
--   $$U(t) \;\le\; 73 \sum_{n} t_n^2.$$
--
--   The proof follows the shape of arXiv:2203.14950, Theorem 1.2: Cauchy–Schwarz gives $U^2 \le V\cdot W$; the expanded square $W$ splits into a diagonal part $S \le 27 V$ (by the $\sigma = 4$ spacing lemma) and an off-diagonal part $T \le 72\,U$ (by the two-point lemma); solving the resulting quadratic inequality yields $U \le 73 V$ with $V = \sum t_n^2$.
--
--   **Role.** This is Step 1 of the eigenvalue-bound argument: it is consumed by `Zeta23.MV.eigen_bound`, which combines it with the Preissmann–Lévêque identity and the $\sigma = 2$ spacing lemma to get $|\mu| \le 13$, the constant behind the project's unconditional Montgomery–Vaughan inequality.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Quadratic.lean#L53-L210

import Mathlib
import Definitions.Def_Zeta23_MV_Quadratic
import Definitions.Def_Zeta23_MV_Spacing

open Real Finset
open scoped BigOperators
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}

theorem Zeta23.MV.Uform_le (h : Adm freq δ) (t : ι → ℝ) (ht : ∀ r, 0 ≤ t r) :
    Uform freq δ t ≤ 73 * ∑ n, t n ^ 2 := by sorry
