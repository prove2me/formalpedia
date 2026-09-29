-- Prove2me | Theorems.Thm_Zeta23_MV_Adm_spacing_four
-- name    : Zeta23.MV.Adm.spacing_four
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:51:23.937065+00:00
-- url     : https://prove2.me/theorems/1ec4fbc1-7d95-4ad9-a70e-464027d934f9
-- title:
--   Spacing lemma, $\sigma = 4$: $\sum_{t \ne s} \delta_t/(\lambda_s - \lambda_t)^4 \le 27/\delta_s^3$
-- statement:
--   Let $\iota$ be a finite index type, $\mathrm{freq} \colon \iota \to \mathbb{R}$ a family of frequencies, and $\delta \colon \iota \to \mathbb{R}$ admissible weights, meaning: $\mathrm{freq}$ is injective, $\delta_r > 0$ for all $r$, and $\delta_r \le |\mathrm{freq}_r - \mathrm{freq}_s|$ for all $r \ne s$ (the shape of the hypotheses of the Montgomery–Vaughan inequality `Zeta23.MVHilbert`). Then for every index $s$,
--
--   $$\sum_{t \ne s} \frac{\delta_t}{(\mathrm{freq}_s - \mathrm{freq}_t)^4} \;\le\; \frac{27}{\delta_s^{3}}.$$
--
--   The proof compares the sum with $\int |u - \mathrm{freq}_s|^{-4}\,du$ over the pairwise disjoint intervals $I_t = (\mathrm{freq}_t - \delta_t/2,\ \mathrm{freq}_t + \delta_t/2)$, using the membership bounds `abs_le_of_mem_itv` and the closed-form integral `integral_inv_four_Icc`.
--
--   **Role.** Together with its $\sigma = 2$ companion, this replaces [Preissmann 1984, Lemme 1] (cited without proof in arXiv:2203.14950) by an elementary argument at a worse but sufficient constant. It is consumed by `Zeta23.MV.Uform_le`, the quadratic-form bound $U \le 73\sum t_n^2$ in the eigenvalue-bound proof of the Montgomery–Vaughan weighted Hilbert inequality.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Spacing.lean#L318-L446

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Adm
variable {freq δ : ι → ℝ} (h : Adm freq δ)

theorem Zeta23.MV.Adm.spacing_four (h : Adm freq δ) (s : ι) :
    ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4 ≤ 27 / δ s ^ 3 := by sorry
