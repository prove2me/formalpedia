-- Prove2me | Theorems.Thm_AnalyticCombinatorics_atom_lcyc_counts_eq_factorial
-- name    : AnalyticCombinatorics.atom_lcyc_counts_eq_factorial
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T21:21:46.570222+00:00
-- url     : https://prove2.me/theorems/91227c24-935f-411f-b740-950d90be899e
-- title:
--   Counting a labelled cycle of atoms
-- statement:
--   For every natural $n\ge1$, the source labelled cycle class built from size-one atoms has $$|\operatorname{LCYC}(\mathcal Z)_n|=(n-1)!.$$ Its cycle objects use the source canonical labelled rotation representative; the positivity premise is retained.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/LabelledCycleCount.lean#L32. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Mathlib
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Composition

namespace AnalyticCombinatorics.Ch5.Meromorphic.Alignments end AnalyticCombinatorics.Ch5.Meromorphic.Alignments

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# The labelled-cycle count `(n-1)!` (F&S §II.2, the CYC logarithm)

The Ch2 cycle construction `CYC` is characterized at the EGF level by the ODE
`CYC(C)' = C'·SEQ(C)` together with a zero constant term
(`CombClass.egf_lcyc_unique`).  For the atomic class `Z` this pins the EGF down to
the **logarithm** `L(z) = log(1/(1-z)) = Σ_{n≥1} zⁿ/n` (`atom_lcyc_egf_eq_cycleEGFℚ`,
with `coeff n cycleEGFℚ = 1/n`).

This file records the resulting *combinatorial* closed form — the signature CYC
fact that an `n`-element labelled set admits exactly `(n-1)!` distinct cyclic
arrangements:

  `atom.lcyc.counts n = (n-1)!`  (`n ≥ 1`).

It is the integer shadow of the analytic identity `[zⁿ] log(1/(1-z)) = 1/n`
read through `[zⁿ] EGF = counts n / n!`, since `n!/n = (n-1)!`.
-/

open PowerSeries

open AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

theorem AnalyticCombinatorics.atom_lcyc_counts_eq_factorial (n : ℕ) (hn : 1 ≤ n) :
    CombClass.atom.lcyc.counts n = (n - 1).factorial := by sorry
