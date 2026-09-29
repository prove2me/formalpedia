-- Prove2me | Theorems.Thm_Zeta23_MV_eigen_bound
-- name    : Zeta23.MV.eigen_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:53:11.015936+00:00
-- url     : https://prove2.me/theorems/225be59f-40f6-4f5c-933c-5cacee1b3dde
-- title:
--   Eigenvalue bound (Step 3): $|\mu| \le 13$ for the normalized Montgomery–Vaughan matrix
-- statement:
--   Let $\iota$ be a finite index type, $\mathrm{freq} \colon \iota \to \mathbb{R}$ a family of frequencies, and $\delta \colon \iota \to \mathbb{R}$ admissible weights, meaning: $\mathrm{freq}$ is injective, $\delta_r > 0$ for all $r$, and $\delta_r \le |\mathrm{freq}_r - \mathrm{freq}_s|$ for all $r \ne s$ (the shape of the hypotheses of the Montgomery–Vaughan inequality `Zeta23.MVHilbert`). Let $u \colon \iota \to \mathbb{C}$ be a unit vector, $\sum_n \|u_n\|^2 = 1$, and let $\mu \in \mathbb{R}$ satisfy the eigen-relation of the normalized kernel (weights $c_r = \sqrt{\delta_r}$):
--
--   $$\sum_{n \ne m} \frac{\sqrt{\delta_m}\,\sqrt{\delta_n}}{\mathrm{freq}_m - \mathrm{freq}_n}\; u_n \;=\; \mu\, i\, u_m \qquad \text{for every } m \in \iota.$$
--
--   Then
--
--   $$|\mu| \;\le\; 13.$$
--
--   The proof sums the Preissmann–Lévêque eigen-identity over $m$, inserts the $\sigma = 2$ spacing lemma ($\le 9$) for the first term and the quadratic-form bound `Uform_le` ($\le 73$) for the second, giving $\mu^2 \le 9 + 2\cdot 73 = 155 \le 13^2$.
--
--   **Role.** This is Step 3, the heart of the project's self-contained proof of the Montgomery–Vaughan weighted Hilbert inequality: it instantiates `EigenBound 13`, from which the spectral reduction produces `MVDiag 13` and, by polarization, the bilinear H-MV hypothesis. It is consumed directly by the top-level assemblies `Zeta23.thmA3` and `Zeta23.thmA3_cumulative` of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Eigen.lean#L44-L138

import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_Zeta23_MV_Spacing

open Real Finset Complex
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}

theorem Zeta23.MV.eigen_bound (h : Adm freq δ) (u : ι → ℂ) (hu : ∑ n, ‖u n‖ ^ 2 = 1) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * u n
          = (μ : ℂ) * Complex.I * u m) :
    |μ| ≤ 13 := by sorry
