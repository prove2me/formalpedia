-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cyclicAPProduct_pos_iff_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:08:48.525258+00:00
-- url     : https://prove2.me/submissions/395150d2-543f-47d7-a3db-951314a43e99

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- For nonnegative weights, a cyclic progression has positive product
exactly when each of its factors is positive. -/
theorem solution
    {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 < cyclicAPProduct k N f a d ↔
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by
  constructor
  · intro hprod j
    have hprod_ne :
        (∏ i : Fin k, f (cyclicAPTerm a d i)) ≠ 0 := by
      simpa only [cyclicAPProduct] using ne_of_gt hprod
    have hfactor_ne : f (cyclicAPTerm a d j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod_ne j (Finset.mem_univ j)
    exact lt_of_le_of_ne (hf _) (Ne.symm hfactor_ne)
  · intro hfactor
    rw [cyclicAPProduct]
    exact Finset.prod_pos fun j _ => hfactor j
