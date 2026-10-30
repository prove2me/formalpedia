-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_SequenceInverse
-- name    : AnalyticCombinatorics_Ch1_OGF_SequenceInverse
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-24T21:22:17.241134+00:00
-- url     : https://prove2.me/theorems/7e3c64b0-4b40-452e-9564-eff4d65f2431
-- title:
--   Adding a first part to an integer composition
-- statement:
--   For a natural number $n$, an integer $k$ with $0\leq k\leq n$, and an ordered composition $c$ of $n-k$, form the ordered composition of $n+1$ whose first part is $k+1$ and whose remaining parts are those of $c$:
--
--   $$\operatorname{consSeq}(n,k,c)=(k+1)\mathbin{::}c.$$
--
--   The positive first part and the total-size identity make this a valid composition. This operation supplies the combinatorial object used to separate a nonempty ordered sequence into its first component and its remainder. The generating-function inverse theorem is a separate theorem target.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/SequenceInverse.lean. Definitions for the sequence-construction portion of Flajolet and Sedgewick, Analytic Combinatorics (Cambridge University Press, 2009), Chapter I. Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
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

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

variable {C : CombClass}

/-- Assemble a composition of `n+1` from a first part of size `k+1` and a
composition of the remaining `n - k`. -/
def consSeq (n : ℕ) (k : Fin (n + 1)) (c : Composition (n - (k : ℕ))) :
    Composition (n + 1) :=
  (Composition.append (Composition.single ((k : ℕ) + 1) (Nat.succ_pos _)) c).cast
    (by have := k.is_le; omega)

end AnalyticCombinatorics.Ch1


