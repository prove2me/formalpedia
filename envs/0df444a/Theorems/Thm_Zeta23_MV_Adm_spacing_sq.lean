-- Prove2me | Theorems.Thm_Zeta23_MV_Adm_spacing_sq
-- name    : Zeta23.MV.Adm.spacing_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:51:42.156825+00:00
-- url     : https://prove2.me/theorems/9da63d38-f4a5-46bd-9a13-2e7ef109480c
-- title:
--   Spacing lemma, $\sigma = 2$: $\sum_{t \ne s} \delta_t/(\lambda_s - \lambda_t)^2 \le 9/\delta_s$
-- statement:
--   Let $\iota$ be a finite index type, $\mathrm{freq} \colon \iota \to \mathbb{R}$ a family of frequencies, and $\delta \colon \iota \to \mathbb{R}$ admissible weights, meaning: $\mathrm{freq}$ is injective, $\delta_r > 0$ for all $r$, and $\delta_r \le |\mathrm{freq}_r - \mathrm{freq}_s|$ for all $r \ne s$ (the shape of the hypotheses of the Montgomery–Vaughan inequality `Zeta23.MVHilbert`). Then for every index $s$,
--
--   $$\sum_{t \ne s} \frac{\delta_t}{(\mathrm{freq}_s - \mathrm{freq}_t)^2} \;\le\; \frac{9}{\delta_s}.$$
--
--   The proof compares the sum with $\int |u - \mathrm{freq}_s|^{-2}\,du$ over the pairwise disjoint intervals $I_t = (\mathrm{freq}_t - \delta_t/2,\ \mathrm{freq}_t + \delta_t/2)$, using the membership bounds `abs_le_of_mem_itv` and the closed-form integral `integral_inv_sq_Icc`.
--
--   **Role.** This replaces [Preissmann 1984, Lemme 1] (cited without proof in arXiv:2203.14950) by an elementary argument at a worse but sufficient constant. It is consumed by the two-point lemma `Zeta23.MV.Adm.two_point` and directly by the eigenvalue bound `Zeta23.MV.eigen_bound` ($\mu^2 \le 9 + 2\cdot 73 = 155 \le 13^2$), the engine of the project's unconditional Montgomery–Vaughan weighted Hilbert inequality.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Spacing.lean#L182-L313

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Adm
variable {freq δ : ι → ℝ} (h : Adm freq δ)
variable (h : Adm freq δ) (s : ι)

theorem Zeta23.MV.Adm.spacing_sq (h : Adm freq δ) (s : ι) :
    ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 2 ≤ 9 / δ s := by sorry
