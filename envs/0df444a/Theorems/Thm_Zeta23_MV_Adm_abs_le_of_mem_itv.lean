-- Prove2me | Theorems.Thm_Zeta23_MV_Adm_abs_le_of_mem_itv
-- name    : Zeta23.MV.Adm.abs_le_of_mem_itv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:49:52.009132+00:00
-- url     : https://prove2.me/theorems/1a65f466-29ae-4d14-8889-baf8d98e148b
-- title:
--   Membership bounds on the interval $I_t$ for admissible weights
-- statement:
--   Let $\iota$ be a finite index type, $\mathrm{freq} \colon \iota \to \mathbb{R}$ a family of frequencies, and $\delta \colon \iota \to \mathbb{R}$ admissible weights, meaning: $\mathrm{freq}$ is injective, $\delta_r > 0$ for all $r$, and $\delta_r \le |\mathrm{freq}_r - \mathrm{freq}_s|$ for all $r \ne s$ (the shape of the hypotheses of the Montgomery–Vaughan inequality `Zeta23.MVHilbert`). Let $I_t = (\mathrm{freq}_t - \delta_t/2,\ \mathrm{freq}_t + \delta_t/2)$ be the open interval around $\mathrm{freq}_t$ (these intervals are pairwise disjoint by admissibility). Suppose $t \ne s$ and $u \in I_t$. Then
--
--   $$|\mathrm{freq}_s - u| \;\le\; \tfrac{3}{2}\,|\mathrm{freq}_s - \mathrm{freq}_t| \qquad \text{and} \qquad \tfrac{\delta_s}{2} \;\le\; |u - \mathrm{freq}_s|.$$
--
--   That is, points of $I_t$ are at controlled distance from any other frequency $\mathrm{freq}_s$: no closer than $\delta_s/2$, and no farther than $3/2$ times the center distance.
--
--   **Role.** This is the key geometric input for the comparison of sums with integrals over the disjoint intervals $I_t$: it is consumed by both spacing lemmas `Zeta23.MV.Adm.spacing_sq` ($\sigma = 2$) and `Zeta23.MV.Adm.spacing_four` ($\sigma = 4$), which in turn drive the eigenvalue bound behind the Montgomery–Vaughan weighted Hilbert inequality.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Spacing.lean#L68-L87

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

theorem Zeta23.MV.Adm.abs_le_of_mem_itv (h : Adm freq δ) {s t : ι} (hts : t ≠ s) {u : ℝ}
    (hu : u ∈ Adm.itv (freq := freq) (δ := δ) t) :
    |freq s - u| ≤ 3 / 2 * |freq s - freq t| ∧ δ s / 2 ≤ |u - freq s| := by sorry
