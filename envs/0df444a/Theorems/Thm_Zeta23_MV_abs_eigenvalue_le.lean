-- Prove2me | Theorems.Thm_Zeta23_MV_abs_eigenvalue_le
-- name    : Zeta23.MV.abs_eigenvalue_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:52:55.67221+00:00
-- url     : https://prove2.me/theorems/85841cdc-8c74-426b-b849-6d47afb5d691
-- title:
--   Eigenvalues of the Hermitian matrix $M = iK$ are bounded by $C$
-- statement:
--   Let $C \in \mathbb{R}$ and assume `EigenBound C`: for every finite index type, every admissible pair $(\mathrm{freq}, \delta)$ (injective frequencies, $\delta_r > 0$, $\delta_r \le |\mathrm{freq}_r - \mathrm{freq}_s|$ for $r \ne s$), every unit vector $u$ ($\sum_n \|u_n\|^2 = 1$) and every real $\mu$ satisfying the eigen-relation
--
--   $$\sum_{n \ne m} \frac{\sqrt{\delta_m}\sqrt{\delta_n}}{\mathrm{freq}_m - \mathrm{freq}_n}\; u_n \;=\; \mu\, i\, u_m \quad \text{for all } m,$$
--
--   one has $|\mu| \le C$. Now fix an admissible pair $(\mathrm{freq}, \delta)$ on a finite index type $\iota$ and let $M = iK$ be the Hermitian matrix with entries $M_{rs} = i\,\sqrt{\delta_r}\sqrt{\delta_s}/(\mathrm{freq}_r - \mathrm{freq}_s)$ for $r \ne s$ and $0$ on the diagonal (`Mmat`; Hermitian since $K$ is real antisymmetric). Then every eigenvalue of $M$, in the sense of Mathlib's `Matrix.IsHermitian.eigenvalues`, satisfies
--
--   $$\bigl|\nu_j\bigr| \;\le\; C \qquad \text{for every } j \in \iota.$$
--
--   The proof feeds each eigenpair from Mathlib's eigenbasis (unit eigenvector) into the eigen-relation of `EigenBound` with $\mu = -\nu_j$.
--
--   **Role.** Step 4 (spectral reduction) of the Montgomery–Vaughan chain: it is consumed by `Zeta23.MV.mvDiag_of_eigenBound`, which expands the Hermitian form in the eigenbasis to obtain the diagonal Montgomery–Vaughan inequality `MVDiag C`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Duality.lean#L105-L144

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

theorem Zeta23.MV.abs_eigenvalue_le {C : ℝ} (hb : EigenBound C) {freq δ : ι → ℝ} (h : Adm freq δ) (j : ι) :
    |(Mmat_isHermitian freq δ).eigenvalues j| ≤ C := by sorry
