-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cfzCoefficient_natAbs_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:44.346285+00:00
-- url     : https://prove2.me/submissions/fb6cd0e5-de24-43cb-aef7-af5fac362f33

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- Every CFZ coefficient has absolute value strictly below `k`, hence at
most `k`. -/
theorem solution {k : ℕ}
    (q : CFZFormIndex k) (v : CFZVariable k) :
    Int.natAbs (cfzCoefficient q v) ≤ k := by
  rw [cfzCoefficient]
  split
  next hneq =>
    split
    next hselected =>
      exact Int.natAbs_coe_sub_coe_le_of_le
        (Nat.le_of_lt v.1.isLt) (Nat.le_of_lt q.1.isLt)
    next hnotselected =>
      simp
  next heq =>
    simp
