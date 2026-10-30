-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_prodPow
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_prodPow
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:24.679493+00:00
-- url     : https://prove2.me/theorems/9d26f91c-73ee-4363-b016-7c846c2f67db
-- title:
--   Cartesian powers raise the ordinary generating function to a power
-- statement:
--   For a graded class $C$ of finite sets, write $c_n=|C_n|$ and $A_C(z)=\sum_{n\ge0}c_nz^n\in\mathbb Q[[z]]$. Let $C^0$ have one size-zero object and let $C^{k+1}=C\times C^k$, with component sizes adding in the product. For every $k\in\mathbb N$,
--
--   $$A_{C^k}(z)=A_C(z)^k.$$
--
--   The case $k=0$ is included.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/ProductPower.lean#L23. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_ProductPower
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.2–I.3 — Cartesian powers and words over a finite alphabet

Flajolet & Sedgewick, Part A, Chapter I. Iterating the product construction gives
the `k`-fold Cartesian power `C^k = C × C × ⋯ × C`, with OGF `C(z)^k` (an immediate
induction from the binary product rule `ogf_prod`). As the standard application,
words of length `k` over an alphabet of `a` letters form `(a·Z)^k`, with OGF
`(a z)^k` (so there are `a^k` of them), recovering F&S §I.3.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_prodPow (C : CombClass) (k : ℕ) :
    (C.prodPow k).ogf = C.ogf ^ k := by sorry
