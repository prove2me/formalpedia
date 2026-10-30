-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_ogf_seq_alphabet
-- name    : AnalyticCombinatorics.Ch1.ogf_seq_alphabet
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:32.658423+00:00
-- url     : https://prove2.me/theorems/7dc181ac-20e7-4c04-83dc-55b9def17ef3
-- title:
--   Ordinary generating function of finite words
-- statement:
--   For $a\in\mathbb N$, let $W_a(z)$ be the ordinary generating function of finite words over an $a$-letter size-one alphabet. Then, as a formal identity over $\mathbb Q$,
--
--   $$W_a(z)(1-az)=1.$$
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/SeqApplications.lean#L39. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_ProductPower
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.3 — Applications of the sequence construction

Flajolet & Sedgewick, Part A, Chapter I, §I.3, applying the general transfer
`SEQ(C)(z) = 1/(1 - C(z))` (`ogf_seq_mul`):

* `counts_seq_alphabet` / `ogf_seq_alphabet` — **words over a finite alphabet**:
  `SEQ` of an `a`-letter alphabet enumerates all words; there are `a^n` of length
  `n`, with OGF `1/(1 - a z)`.
* `ogf_seq_posInt` — **compositions revisited**: the special case `C = ℙ`
  recovers `(seq ℙ)(z)·(1 - ℙ(z)) = 1` as an instance of the general theorem
  (cf. the bespoke proof in `SeqFormula.lean`).
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.ogf_seq_alphabet (a : ℕ) :
    (CombClass.alphabet a).seq.ogf * (1 - (a : ℕ) • X) = 1 := by sorry
