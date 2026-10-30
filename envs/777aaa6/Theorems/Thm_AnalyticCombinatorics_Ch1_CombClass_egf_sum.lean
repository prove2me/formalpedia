-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_egf_sum
-- name    : AnalyticCombinatorics.Ch1.CombClass.egf_sum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:58:47.220573+00:00
-- url     : https://prove2.me/theorems/4597bb39-2723-4d09-8c29-dbed327a223f
-- title:
--   Disjoint unions add exponential generating functions
-- statement:
--   For a graded class $C$ with finite size fibres, write $E_C(z)=\sum_{n\ge0}|C_n|z^n/n!\in\mathbb Q[[z]]$. For arbitrary graded classes $A,B$, form $(A+B)_n=A_n\sqcup B_n$. Then
--
--   $$E_{A+B}(z)=E_A(z)+E_B(z).$$
--
--   Every coefficient uses the same factor $1/n!$.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledSum.lean#L19. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sum
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch2 §II.1 — The labelled sum

Flajolet & Sedgewick, Part A, Chapter II. The combinatorial sum (disjoint union)
is the same construction for labelled and unlabelled classes (it reuses
`CombClass.sum`); only the translation to the EGF differs:

  **`(A + B)(z) = A(z) + B(z)`**.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.CombClass.egf_sum (A B : CombClass) :
    (A.sum B).egf = A.egf + B.egf := by sorry
