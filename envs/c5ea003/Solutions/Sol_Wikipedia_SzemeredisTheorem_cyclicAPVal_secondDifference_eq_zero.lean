-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cyclicAPVal_secondDifference_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:08:48.502068+00:00
-- url     : https://prove2.me/submissions/3341d710-edfd-4aae-a393-3e459bcbcdd5

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Unwrapping cyclic progressions in a short interval

A progression obtained by transference lives in `ZMod N`.  The prime weight
is supported on an interval much shorter than a full residue system.  In
that situation the standard representatives have second difference zero
over the integers, so they form an ordinary integer progression.
-/

namespace Wikipedia.SzemeredisTheorem



@[simp]
theorem cyclicAPVal_cast {N : ℕ} [NeZero N]
    (a d : ZMod N) (j : ℕ) :
    (cyclicAPVal a d j : ZMod N) = a + (j : ZMod N) * d :=
  ZMod.natCast_zmod_val _

/-- Three points in an integer interval of width `U-L` have second
difference of absolute value at most twice that width. -/
theorem abs_secondDifference_le {L U z₀ z₁ z₂ : ℤ}
    (hz₀ : L ≤ z₀ ∧ z₀ ≤ U)
    (hz₁ : L ≤ z₁ ∧ z₁ ≤ U)
    (hz₂ : L ≤ z₂ ∧ z₂ ≤ U) :
    |z₂ - 2 * z₁ + z₀| ≤ 2 * (U - L) := by
  rw [abs_le]
  constructor <;> linarith











end Wikipedia.SzemeredisTheorem

end
/-!
# Unwrapping cyclic progressions in a short interval

A progression obtained by transference lives in `ZMod N`.  The prime weight
is supported on an interval much shorter than a full residue system.  In
that situation the standard representatives have second difference zero
over the integers, so they form an ordinary integer progression.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- The standard representatives of a cyclic progression supported in an
interval of width less than `N/2` have vanishing integer second
differences. -/
theorem solution {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (hmem :
      ∀ i : ℕ, i < k →
        L ≤ cyclicAPVal a d i ∧ cyclicAPVal a d i ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (j : ℕ) (hj : j + 2 < k) :
    (cyclicAPVal a d (j + 2) : ℤ) -
        2 * cyclicAPVal a d (j + 1) +
        cyclicAPVal a d j = 0 := by
  let z : ℤ :=
    (cyclicAPVal a d (j + 2) : ℤ) -
      2 * cyclicAPVal a d (j + 1) +
      cyclicAPVal a d j
  apply Int.eq_zero_of_abs_lt_dvd (m := (N : ℤ)) (x := z)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    dsimp [z]
    push_cast
    simp only [cyclicAPVal_cast, Nat.cast_add, Nat.cast_ofNat]
    ring
  · exact lt_of_le_of_lt
      (abs_secondDifference_le
        (hmem j (by omega))
        (hmem (j + 1) (by omega))
        (hmem (j + 2) hj))
      hwidth
