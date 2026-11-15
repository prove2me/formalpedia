-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.containsAP_of_cyclicAPVal_shortInterval
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:44.229913+00:00
-- url     : https://prove2.me/submissions/773f4fa5-a228-46d1-b07f-256e0040eb1b

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPVal_secondDifference_eq_zero
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eq_affine_of_secondDifference_zero

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











/-- Short support converts all standard representatives of a cyclic
progression into one ordinary integer affine progression. -/
theorem cyclicAPVal_eq_affine {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (hmem :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ)) :
    ∀ j : ℕ, j < k →
      (cyclicAPVal a d j : ℤ) =
        cyclicAPVal a d 0 +
          (j : ℤ) *
            ((cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0) := by
  apply eq_affine_of_secondDifference_zero
  intro j hj
  exact cyclicAPVal_secondDifference_eq_zero a d L U hmem hwidth j hj

/-- A nonzero cyclic common difference gives distinct zeroth and first
standard representatives. -/
theorem cyclicAPVal_one_sub_zero_ne_zero {N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) :
    (cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0 ≠ 0 := by
  intro hzero
  have hval : cyclicAPVal a d 1 = cyclicAPVal a d 0 := by
    exact_mod_cast sub_eq_zero.mp hzero
  have had : a + d = a := by
    apply ZMod.val_injective N
    simpa [cyclicAPVal] using hval
  apply hd
  apply add_left_cancel (a := a)
  simpa using had

/-- The integer common difference exposed by short-interval unwrapping is
nonzero whenever the cyclic difference is nonzero. -/
theorem cyclicAPVal_isIntegerAP {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (L U : ℤ)
    (hmem :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ)) :
    ∃ s : ℤ, s ≠ 0 ∧
      ∀ j : ℕ, j < k →
        (cyclicAPVal a d j : ℤ) =
          cyclicAPVal a d 0 + (j : ℤ) * s := by
  refine ⟨(cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0,
    cyclicAPVal_one_sub_zero_ne_zero a d hd, ?_⟩
  exact cyclicAPVal_eq_affine a d L U hmem hwidth

end Wikipedia.SzemeredisTheorem

end
/-!
# Lifting a short cyclic progression to the natural numbers

After unwrapping a cyclic progression, its integer common difference can
have either orientation.  A positive difference already gives the required
natural-number progression.  A negative difference gives the same
progression after reversing its `k` terms.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- A nonconstant cyclic progression whose standard representatives lie in a
short interval and in `A` yields a positive-step natural-number progression
in `A`.  When the unwrapped integer step is negative, the witnesses are
obtained by reversing the indices `j ↦ k - 1 - j`. -/
theorem solution
    {A : Set ℕ} {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (hk : 2 ≤ k)
    (L U : ℤ)
    (hinterval :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (hA : ∀ j : ℕ, j < k → cyclicAPVal a d j ∈ A) :
    ContainsAP A k := by
  obtain ⟨s, hs, haffine⟩ :=
    cyclicAPVal_isIntegerAP a d hd L U hinterval hwidth
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · let step : ℕ := (-s).toNat
    have hstep_cast : (step : ℤ) = -s := by
      exact Int.natCast_toNat_eq_self.mpr (neg_nonneg.mpr hsneg.le)
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d (k - 1), step, hstep_pos, ?_⟩
    intro j hj
    have hlast : k - 1 < k := by omega
    have hrev : k - 1 - j < k := by omega
    have hindex :
        ((k - 1 - j : ℕ) : ℤ) =
          (k - 1 : ℕ) - (j : ℤ) := by
      omega
    have hterm :
        cyclicAPVal a d (k - 1) + step * j =
          cyclicAPVal a d (k - 1 - j) := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine (k - 1) hlast,
        haffine (k - 1 - j) hrev, hindex]
      ring
    rw [hterm]
    exact hA (k - 1 - j) hrev
  · let step : ℕ := s.toNat
    have hstep_cast : (step : ℤ) = s := by
      exact Int.natCast_toNat_eq_self.mpr hspos.le
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d 0, step, hstep_pos, ?_⟩
    intro j hj
    have hterm :
        cyclicAPVal a d 0 + step * j = cyclicAPVal a d j := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine j hj]
      ring
    rw [hterm]
    exact hA j hj
