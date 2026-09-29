-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_covariance_degenerate
-- name    : MarkovChainCLT.abs_covariance_degenerate
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:22:57.407704+00:00
-- url     : https://prove2.me/theorems/cbbda789-a9b9-434f-a9fc-fd3ad8eb022d
-- title:
--   Pairwise $\varphi$-bound in the degenerate case
-- statement:
--   Degenerate case of the pairwise $\varphi$-covariance bound.
--
--   Let $U$ be past-measurable and $V$ future-measurable at lag $n$, both square-integrable. If $\mathrm{Var}(U)=0$ or $\mathrm{Var}(V)=0$, then
--
--   $$
--   |\mathrm{Cov}(U,V)|\le 2\sqrt{\varphi(n)}\sqrt{\mathrm{Var}(U)}\sqrt{\mathrm{Var}(V)}.
--   $$
--
--   Indeed Cauchy-Schwarz forces $\mathrm{Cov}(U,V)=0$ while the right side is nonnegative. Splitting off this zero-variance case (where correlation quotients are $0/0$) isolates the content of the full bound in the strictly positive-variance regime.
--
--   **Formalization Note** Uses `cov_abs_le_sqrt_var` and nonnegativity of the right side.
-- source:
--   Degenerate case split for Ibragimov covariance inequality, cf. Bradley survey eq. (1.13); Cauchy-Schwarz step

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_cov_abs_le_sqrt_var

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.abs_covariance_degenerate {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ) (U V : Ω → ℝ) (hU : Measurable[processSigma Y (Set.Iic k)] U) (hV : Measurable[processSigma Y (Set.Ici (k + n))] V) (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P) (hdeg : Var[U; P] = 0 ∨ Var[V; P] = 0) : |cov[U, V; P]| ≤ 2 * Real.sqrt (phiMixingCoef P Y n) * (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) := by sorry
