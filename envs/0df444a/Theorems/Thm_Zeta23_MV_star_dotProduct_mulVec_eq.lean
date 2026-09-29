-- Prove2me | Theorems.Thm_Zeta23_MV_star_dotProduct_mulVec_eq
-- name    : Zeta23.MV.star_dotProduct_mulVec_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:54:05.828285+00:00
-- url     : https://prove2.me/theorems/0cbd2473-a4cb-4713-90d9-b84ce0620ed6
-- title:
--   Spectral expansion $x^* A x = \sum_i \nu_i \,|(U^* x)_i|^2$ for a Hermitian matrix
-- statement:
--   Let $A$ be a Hermitian matrix over $\mathbb{C}$ indexed by a finite type $\iota$, with real eigenvalues $\nu_i$ (Mathlib's `Matrix.IsHermitian.eigenvalues`) and eigenvector unitary $U$ (`Matrix.IsHermitian.eigenvectorUnitary`, the unitary whose columns form an orthonormal eigenbasis). Then for every complex vector $x \colon \iota \to \mathbb{C}$, the Hermitian form expands spectrally:
--   $$x^* A x \;=\; \sum_i \nu_i \,\bigl\| (U^* x)_i \bigr\|^2 ,$$
--   where the left side is the complex number $\overline{x} \cdot (A x)$ (Lean's `star x ⬝ᵥ (A *ᵥ x)`) and the right side is a real sum coerced to $\mathbb{C}$ — in particular the identity records that the Hermitian form is real-valued.
--
--   This lemma lives in the spectral-reduction step of the Montgomery–Vaughan argument (module `Zeta23.MV.Duality`): expanding $y^* M y$ in the eigenbasis of the Hermitian matrix $M = iK$ is what converts the eigenvalue bound $|\nu| \le 13$ into the diagonal Montgomery–Vaughan inequality, via its consumer `Zeta23.MV.mvDiag_of_eigenBound`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Duality.lean#L72-L90

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

theorem Zeta23.MV.star_dotProduct_mulVec_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ x)
      = ((∑ i, hA.eigenvalues i *
          ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by sorry
