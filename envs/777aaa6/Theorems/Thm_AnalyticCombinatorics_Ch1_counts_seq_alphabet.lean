-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_counts_seq_alphabet
-- name    : AnalyticCombinatorics.Ch1.counts_seq_alphabet
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:24.864058+00:00
-- url     : https://prove2.me/theorems/7870fcb4-ddb3-4d48-b143-87f3598e92f0
-- title:
--   Counting words over a finite alphabet
-- statement:
--   Let $a,n\in\mathbb N$. The alphabet class has $a$ objects of size one and no objects of any other size; its finite sequence construction consists of ordered lists whose sizes sum to $n$. Then
--
--   $$|\operatorname{SEQ}(\operatorname{Alphabet}_a)_n|=a^n.$$
--
--   Both zero values are included, with the empty word counted once.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/SeqApplications.lean#L25. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch1.counts_seq_alphabet (a n : ℕ) :
    (CombClass.alphabet a).seq.counts n = a ^ n := by sorry
