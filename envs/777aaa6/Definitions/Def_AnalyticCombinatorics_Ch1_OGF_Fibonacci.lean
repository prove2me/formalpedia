-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
-- name    : AnalyticCombinatorics_Ch1_OGF_Fibonacci
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-24T21:22:45.203654+00:00
-- url     : https://prove2.me/theorems/ce0fa0e0-6aed-4d68-94e8-380de0fb32d6
-- title:
--   The combinatorial class of parts of sizes one and two
-- statement:
--   The class $D$ has exactly one object of size $1$, exactly one object of size $2$, and no objects of any other size. Its size classes are specified by
--
--   $$\#D_n=\begin{cases}1&n=1\text{ or }n=2,\\0&\text{otherwise}.\end{cases}$$
--
--   Finite ordered sequences of these objects represent compositions into parts of sizes one and two. The class is the input to the separate Fibonacci counting and formal generating-function theorems.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Fibonacci.lean. Definitions for the sequence-construction portion of Flajolet and Sedgewick, Analytic Combinatorics (Cambridge University Press, 2009), Chapter I. Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
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

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The class with one object of size `1` and one of size `2` (parts of a
composition into `1`s and `2`s). -/
def CombClass.parts12 : CombClass where
  Obj n := Fin (if n = 1 then 1 else if n = 2 then 1 else 0)
  finObj _ := inferInstance

end AnalyticCombinatorics.Ch1


