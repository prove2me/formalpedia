-- Prove2me | Theorems.Thm_Zeta23_MV_Adm_abs_bounds_closed
-- name    : Zeta23.MV.Adm.abs_bounds_closed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:49:34.437473+00:00
-- url     : https://prove2.me/theorems/d7f363e8-13ef-4045-9d0b-b791a9a1f535
-- title:
--   Membership bounds on the closed interval $\bar I_t$ for admissible weights
-- statement:
--   Let $\iota$ be a finite index type, $\mathrm{freq} \colon \iota \to \mathbb{R}$ a family of frequencies, and $\delta \colon \iota \to \mathbb{R}$ admissible weights, meaning: $\mathrm{freq}$ is injective, $\delta_r > 0$ for all $r$, and $\delta_r \le |\mathrm{freq}_r - \mathrm{freq}_s|$ for all $r \ne s$ (the shape of the hypotheses of the Montgomery–Vaughan inequality `Zeta23.MVHilbert`). Suppose $t \ne s$ and $u \in \mathbb{R}$ lies in the closed interval of radius $\delta_t/2$ around $\mathrm{freq}_t$, i.e. $|u - \mathrm{freq}_t| \le \delta_t/2$. Then
--
--   $$|\mathrm{freq}_s - u| \;\le\; \tfrac{3}{2}\,|\mathrm{freq}_s - \mathrm{freq}_t| \qquad \text{and} \qquad \tfrac{\delta_s}{2} \;\le\; |u - \mathrm{freq}_s|.$$
--
--   That is, a point of the closed interval $\bar I_t$ is comparable in distance to $\mathrm{freq}_s$ with the center $\mathrm{freq}_t$, and stays at least $\delta_s/2$ away from $\mathrm{freq}_s$.
--
--   **Role.** This is the closed-interval version of `Zeta23.MV.Adm.abs_le_of_mem_itv` (which is stated for the open intervals $I_t$), recorded for use on closures $\bar I_t$ in the spacing arguments of `Zeta23.MV.Spacing` — the module that replaces Preissmann's Lemmes 1 and 6 by elementary integral-comparison proofs for the Montgomery–Vaughan step of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Spacing.lean#L127-L144

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Adm
variable {freq δ : ι → ℝ} (h : Adm freq δ)
omit [Fintype ι] [DecidableEq ι]

theorem Zeta23.MV.Adm.abs_bounds_closed (h : Adm freq δ) {s t : ι} (hts : t ≠ s) {u : ℝ}
    (hut : |u - freq t| ≤ δ t / 2) :
    |freq s - u| ≤ 3 / 2 * |freq s - freq t| ∧ δ s / 2 ≤ |u - freq s| := by sorry
