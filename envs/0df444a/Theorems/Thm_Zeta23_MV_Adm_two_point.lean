-- Prove2me | Theorems.Thm_Zeta23_MV_Adm_two_point
-- name    : Zeta23.MV.Adm.two_point
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:52:00.911659+00:00
-- url     : https://prove2.me/theorems/753568d0-d8a6-42c6-a5f9-74226cbb9980
-- title:
--   Two-point lemma: $\sum_{k \ne \ell, m} \frac{\delta_k}{(\lambda_k-\lambda_\ell)^2(\lambda_k-\lambda_m)^2} \le \frac{36(\delta_\ell+\delta_m)}{\delta_\ell \delta_m (\lambda_\ell-\lambda_m)^2}$
-- statement:
--   Let $\iota$ be a finite index type, $\mathrm{freq} \colon \iota \to \mathbb{R}$ a family of frequencies, and $\delta \colon \iota \to \mathbb{R}$ admissible weights, meaning: $\mathrm{freq}$ is injective, $\delta_r > 0$ for all $r$, and $\delta_r \le |\mathrm{freq}_r - \mathrm{freq}_s|$ for all $r \ne s$ (the shape of the hypotheses of the Montgomery–Vaughan inequality `Zeta23.MVHilbert`). Then for any two distinct indices $\ell \ne m$,
--
--   $$\sum_{k \ne \ell,\, m} \frac{\delta_k}{(\mathrm{freq}_k - \mathrm{freq}_\ell)^2\,(\mathrm{freq}_k - \mathrm{freq}_m)^2} \;\le\; \frac{36\,(\delta_\ell + \delta_m)}{\delta_\ell\, \delta_m\, (\mathrm{freq}_\ell - \mathrm{freq}_m)^2},$$
--
--   the sum running over all indices $k$ distinct from both $\ell$ and $m$.
--
--   **Role.** This replaces [Preissmann 1984, Lemme 6] (cited without proof in arXiv:2203.14950) by an elementary argument, at the constant 36. It controls the off-diagonal part in the Cauchy–Schwarz step of `Zeta23.MV.Uform_le` (the quadratic-form bound $U \le 73 \sum t_n^2$), which drives the eigenvalue bound $|\mu| \le 13$ and hence the project's unconditional Montgomery–Vaughan weighted Hilbert inequality.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Spacing.lean#L448-L539

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Adm
variable {freq δ : ι → ℝ} (h : Adm freq δ)

theorem Zeta23.MV.Adm.two_point (h : Adm freq δ) {l m : ι} (hlm : l ≠ m) :
    ∑ k ∈ (Finset.univ.erase l).erase m,
        δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
      ≤ 36 * (δ l + δ m) / (δ l * δ m * (freq l - freq m) ^ 2) := by sorry
