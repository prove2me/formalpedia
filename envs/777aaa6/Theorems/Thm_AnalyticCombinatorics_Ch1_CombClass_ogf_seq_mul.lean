-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_seq_mul
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_seq_mul
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-24T21:23:24.095986+00:00
-- url     : https://prove2.me/theorems/769e0264-d2f9-41a8-b4a0-880b28619721
-- title:
--   The ordinary generating function of ordered sequences
-- statement:
--   Let $C$ be a combinatorial class with finitely many objects of each natural-number size, and assume that it has no objects of size zero. Write $C(X)$ for its ordinary generating function over $\mathbb{Q}$ and $S(X)$ for the ordinary generating function of finite ordered sequences of its objects, with total size given by the sum of component sizes. Then
--
--   $$S(X)(1-C(X))=1.$$
--
--   The sequence class includes the unique empty sequence of total size zero. This general construction rule provides the formal inverse identity used by concrete sequence-counting examples.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/SequenceInverse.lean#L127. General sequence construction; book theorem numbering and page numbers are not asserted. Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
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
# Ch1 §I.2 — The sequence construction: `SEQ(C)(z) = 1/(1 - C(z))`

Flajolet & Sedgewick, Part A, Chapter I, §I.2, the sequence construction, for a
general class `C` with no object of size `0` (`C.counts 0 = 0`). A sequence
decomposes as `SEQ(C) = ε + C × SEQ(C)` (empty, or first component × rest), so the
counting sequence satisfies a convolution recursion and the OGF satisfies the
functional equation `S(z) = 1 + C(z)·S(z)`, hence

  **`(seq C).ogf · (1 - C.ogf) = 1`**, i.e. `SEQ(C)(z) = 1/(1 - C(z))`.

The combinatorial core is the first-part decomposition of compositions, built from
Mathlib's `Composition.append`/`single`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries Finset

variable {C : CombClass}

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_seq_mul (hC0 : C.counts 0 = 0) :
    C.seq.ogf * (1 - C.ogf) = 1 := by sorry
