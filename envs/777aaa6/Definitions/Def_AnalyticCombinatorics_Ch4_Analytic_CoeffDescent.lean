-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_CoeffDescent
-- name    : AnalyticCombinatorics_Ch4_Analytic_CoeffDescent
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:32.352989+00:00
-- url     : https://prove2.me/theorems/fec3df40-8eac-4e83-bfbb-daada1f794da
-- title:
--   Scalar derivatives of formal multilinear series
-- statement:
--   Scalar derivative series evaluate the derivative multilinear map at the scalar one; repeated differentiation is defined recursively, preserving the actual Taylor coefficient representation.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/CoeffDescent.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Coefficient descent and general O-transfer

This file bootstraps the already-proved `β > 1` O-transfer theorem to all real
`β`.  The key bookkeeping device is the scalar one-variable derivative series:
take Mathlib's Frechet derivative series and apply it to `1`.
-/

open Complex Filter Asymptotics
open scoped Topology Real ENNReal BigOperators

noncomputable section

/-- The scalar one-variable derivative series associated to a scalar FMLS. -/
def scalarDerivSeries (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries p.derivSeries

/-- The scalar FMLS for the `k`-th iterated derivative. -/
def scalarIteratedDerivSeries (k : ℕ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  match k with
  | 0 => p
  | k + 1 => scalarDerivSeries (scalarIteratedDerivSeries k p)

end


