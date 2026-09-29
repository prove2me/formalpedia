-- Prove2me | solution 1 for Transreal.add_fin_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T05:36:52.827678+00:00
-- url     : https://prove2.me/submissions/91debef0-227f-4598-81c7-b993fe4d5637

/-
# `Transreal.add_fin_zero`
Target `62a16eee` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`Transreal` is a four-constructor inductive: `fin ℝ | pinf | ninf | null`, and `add` is defined by
explicit case analysis with `null` absorbing. The claim `a + fin 0 = a` splits four ways, and the
CLAUSE ORDER decides how each closes (first match wins):

  a = null : fires the FIRST clause `null, _ => null`  — absorbing        -> rfl
  a = pinf : fires `pinf, fin _ => pinf`, reached only after four earlier
             clauses fail to match                                       -> rfl
  a = ninf : fires `ninf, fin _ => ninf`                                 -> rfl
  a = fin x: fires `fin x, fin y => fin (x + y)`, leaving `fin (x + 0)`  -> add_zero

The clause order was modelled with first-match semantics and checked case by case before drafting;
all four reduce as above. NOTE the claim is RIGHT-sided (`a + fin 0`), which is what the cases
cover — the left-sided form fires different clauses.

The bundle retains NO theorems (skeleton subtraction stripped them all), so nothing here is cited
from it; only the definitions are used.
-/
import Mathlib
import Definitions.Def_Cryptography_Transreal_Core

set_option autoImplicit false
set_option maxHeartbeats 400000

open Transreal in
/-- **The target, verbatim.** -/
theorem solution (a : Transreal) : a + fin 0 = a := by
  cases a with
  | fin x =>
      show Transreal.add (Transreal.fin x) (Transreal.fin 0) = Transreal.fin x
      simp [Transreal.add]
  | pinf => rfl
  | ninf => rfl
  | null => rfl
