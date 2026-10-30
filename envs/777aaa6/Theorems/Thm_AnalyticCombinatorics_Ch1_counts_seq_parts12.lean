-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_counts_seq_parts12
-- name    : AnalyticCombinatorics.Ch1.counts_seq_parts12
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-24T21:23:15.702326+00:00
-- url     : https://prove2.me/theorems/ce7cb098-2384-4eaf-bf97-19605fb1eb38
-- title:
--   Compositions into ones and twos are counted by Fibonacci numbers
-- statement:
--   Let $D$ be the combinatorial class with one object of size $1$, one object of size $2$, and no objects of any other size. For every natural number $n$, including $n=0$, the number of finite ordered sequences of $D$-objects of total size $n$ is
--
--   $$\#\operatorname{SEQ}(D)_n=F_{n+1},$$
--
--   where $F_0=0$ and $F_1=1$ define the initial Fibonacci numbers. The size-zero sequence is the empty sequence. This identifies a concrete sequence construction with a familiar counting sequence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Fibonacci.lean#L48. Repository exposition attributes this construction to Flajolet and Sedgewick, Analytic Combinatorics, Part A, Chapter I, §I.3; no independently numbered book theorem is asserted. Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Mathlib.Data.Nat.Fib.Basic
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
# Ch1 §I.3 — Fibonacci numbers as compositions into parts `1` and `2`

Flajolet & Sedgewick, Part A, Chapter I, §I.3. Let `D` be the class with one
object of size `1` and one of size `2`. Then `SEQ(D)` enumerates compositions of
`n` into parts of size `1` and `2`, and

* `counts_seq_parts12` — there are `F_{n+1}` of them (`Nat.fib (n+1)`), via the
  convolution recursion `counts_seq_succ`, which here is the Fibonacci recurrence;
* `ogf_parts12` / `ogf_seq_parts12` — `D(z) = z + z²` and the OGF is
  `1/(1 - z - z²)`, the Fibonacci generating function.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

theorem AnalyticCombinatorics.Ch1.counts_seq_parts12 (n : ℕ) :
    CombClass.parts12.seq.counts n = Nat.fib (n + 1) := by sorry
