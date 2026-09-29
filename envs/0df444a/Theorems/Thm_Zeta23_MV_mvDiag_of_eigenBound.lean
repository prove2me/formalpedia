-- Prove2me | Theorems.Thm_Zeta23_MV_mvDiag_of_eigenBound
-- name    : Zeta23.MV.mvDiag_of_eigenBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:53:49.134312+00:00
-- url     : https://prove2.me/theorems/ba4fc2f1-1747-48dd-89db-fe2cde52c5ac
-- title:
--   Spectral reduction: an eigenvalue bound yields the diagonal Montgomery–Vaughan inequality
-- statement:
--   Let $C \in \mathbb{R}$. The hypothesis `EigenBound C` states that for every finite index type, every admissible pair $(\mathrm{freq}, \delta)$ (injective frequencies, $\delta_r > 0$, $\delta_r \le |\mathrm{freq}_r - \mathrm{freq}_s|$ for $r \ne s$), every unit vector $u$ and every real $\mu$ satisfying the eigen-relation $\sum_{n \ne m} \frac{\sqrt{\delta_m}\sqrt{\delta_n}}{\mathrm{freq}_m - \mathrm{freq}_n} u_n = \mu i\, u_m$ (all $m$), one has $|\mu| \le C$. The conclusion `MVDiag C` is the literature (diagonal) form of the Montgomery–Vaughan weighted Hilbert inequality: for every finite index type, admissible $(\mathrm{freq}, \delta)$, and complex vector $x$,
--
--   $$\Bigl\| \sum_{r \ne s} \frac{x_r\, \overline{x_s}}{\mathrm{freq}_r - \mathrm{freq}_s} \Bigr\| \;\le\; C\, \sum_r \frac{\|x_r\|^2}{\delta_r}.$$
--
--   The theorem proves `EigenBound C` $\Rightarrow$ `MVDiag C`. Proof: with $M = iK$, $K_{rs} = \sqrt{\delta_r}\sqrt{\delta_s}/(\mathrm{freq}_r - \mathrm{freq}_s)$ off the diagonal, $M$ is Hermitian and every eigenvalue has modulus $\le C$ (`abs_eigenvalue_le`); expanding $y^* M y$ in Mathlib's eigenbasis gives $|y^* M y| \le C \|y\|^2$, and substituting $y_r = x_r/\sqrt{\delta_r}$ lands exactly on the displayed inequality.
--
--   **Role.** This closes the spectral part of the project's self-contained Montgomery–Vaughan proof: combined with `eigen_bound` ($C = 13$) and the polarization step `MVHilbert_of_diag`, it discharges the H-MV hypothesis unconditionally. It is consumed by the top-level assemblies `Zeta23.thmA3` and `Zeta23.thmA3_cumulative` of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Duality.lean#L156-L193

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_MV
import Definitions.Def_Zeta23_MV_Duality
import Definitions.Def_Zeta23_MV_Spacing

open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Zeta23.MV.mvDiag_of_eigenBound {C : ℝ} (hb : EigenBound C) : MVDiag C := by sorry
