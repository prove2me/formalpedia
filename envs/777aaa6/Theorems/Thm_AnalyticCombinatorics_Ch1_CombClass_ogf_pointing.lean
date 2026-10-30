-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_pointing
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_pointing
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:26.199465+00:00
-- url     : https://prove2.me/theorems/65f8e9a7-d65c-43aa-95f6-4da4fc752e0c
-- title:
--   Pointing corresponds to the formal operator z times differentiation
-- statement:
--   For a graded class $C$ of finite sets, write $c_n=|C_n|$ and $A_C(z)=\sum_{n\ge0}c_nz^n\in\mathbb Q[[z]]$. Define the pointed fibre by $\Theta(C)_n=C_n\times\{0,\ldots,n-1\}$. Then
--
--   $$A_{\Theta(C)}(z)=z\,\frac{d}{dz}A_C(z).$$
--
--   Pointing here means precisely this finite choice; no extra structure on a $C$-object is required.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Pointing.lean#L35. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Pointing
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.6 — The pointing construction Θ

Flajolet & Sedgewick, Part A, Chapter I. The *pointing* of a class `C`,
`Θ(C)`, distinguishes one of the `n` atoms of a size-`n` object: a pointed object
is a `C`-object together with a choice of one of its `n` atoms. Hence
`Θ(C)ₙ = n·Cₙ`, and the OGF is

  **`Θ(C)(z) = z·C'(z)`**

(the operator `z d/dz`). We model the pointed objects by `C.Obj n × Fin n`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_pointing (C : CombClass) :
    C.pointing.ogf = X * PowerSeries.derivativeFun C.ogf := by sorry
