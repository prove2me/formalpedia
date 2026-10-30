-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_sum
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_sum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:28.673814+00:00
-- url     : https://prove2.me/theorems/c4394118-5849-4d77-9c68-4207763fd09e
-- title:
--   Disjoint unions add ordinary generating functions
-- statement:
--   For a graded class $C$ of finite sets, write $c_n=|C_n|$ and $A_C(z)=\sum_{n\ge0}c_nz^n\in\mathbb Q[[z]]$. For arbitrary classes $C,D$, let $(C+D)_n=C_n\sqcup D_n$. Then
--
--   $$A_{C+D}(z)=A_C(z)+A_D(z).$$
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Sum.lean#L34. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sum
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.2 — The combinatorial sum (disjoint union) construction

Flajolet & Sedgewick, Part A, Chapter I, §I.2, first admissible construction.
If `A = B + C` is the disjoint union of two combinatorial classes (an object of
size `n` is a `B`-object of size `n` *or* a `C`-object of size `n`), then the
counting sequences add, `Aₙ = Bₙ + Cₙ`, and hence the OGFs add:

  **`(B + C)(z) = B(z) + C(z)`**   (part of F&S Theorem I.1).

The combinatorial content is the `Fintype.card` identity `counts_sum`; the
generating-function identity `ogf_sum` is its image under `ogfSeq`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_sum (C D : CombClass) :
    (C.sum D).ogf = C.ogf + D.ogf := by sorry
