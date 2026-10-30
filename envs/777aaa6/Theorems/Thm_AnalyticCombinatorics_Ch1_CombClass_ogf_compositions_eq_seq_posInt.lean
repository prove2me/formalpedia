-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_compositions_eq_seq_posInt
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_compositions_eq_seq_posInt
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:19.320807+00:00
-- url     : https://prove2.me/theorems/32211e43-29db-4574-b592-bcd17a3e8a90
-- title:
--   Integer compositions as sequences of positive parts
-- statement:
--   Let $C(z)$ be the ordinary generating function of the source class of ordered compositions of a nonnegative integer, including the empty composition. Let $P(z)=\sum_{m\ge1}z^m$ be the ordinary generating function of the class with one object of each positive size. Then
--
--   $$C(z)(1-P(z))=1.$$
--
--   This is the polynomial-form sequence identity; no analytic convergence is assumed.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/SeqFormula.lean#L55. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.3 — The sequence formula, demonstrated on integer compositions

Flajolet & Sedgewick, Part A, Chapter I, §I.3. The symbolic method predicts that
the sequence construction translates to `SEQ(C)(z) = 1/(1 - C(z))`. Here we verify
that prediction end-to-end for the running example `compositions = SEQ(ℙ)`:

* `ogf_posInt` — the OGF of the positive integers is `ℙ(z) = z/(1-z)`, in the form
  `ℙ(z)·(1 - z) = z`.
* `ogf_compositions_eq_seq_posInt` — **`C(z)·(1 - ℙ(z)) = 1`**, i.e.
  `C(z) = 1/(1 - ℙ(z))`, the sequence formula for compositions.

Both are obtained from the two independently-computed closed forms
(`ogf_posInt` here and `ogf_compositions` in `Compositions.lean`) by power-series
algebra and cancellation of the unit `1 - z`; neither assumes the convolution
recursion. The fully-general transfer `SEQ(C)(z) = (1 - C(z))⁻¹` for an arbitrary
class is left to a later milestone (it needs a first-part decomposition bijection
on `Composition`).
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_compositions_eq_seq_posInt :
    CombClass.compositions.ogf * (1 - CombClass.posInt.ogf) = 1 := by sorry
