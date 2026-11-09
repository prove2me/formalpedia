-- Prove2me | solution 1 for Couret.CayleyDoublet.odd_ell_of_odd_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:52.712203+00:00
-- url     : https://prove2.me/submissions/e47ba221-24ea-4de4-a8de-bac37f872651

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 -- canonical order-three return in the odd cyclic quotient.
Research source, **UNCOMPILED** with pinned Lean 4.29.1.
No existing certified theorem has been modified.

The first lemma needs only the order of alpha and a bounded coordinate,
and is independent of any representation of a directed graph. The last
lemma translates its canonical witness back to the quotient G/<h>.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyCanonical







end Couret.CayleyCanonical

namespace Couret.CayleyDoublet

open Couret.CayleyCanonical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]




/-- Oddness of the quotient order 3*ell forces ell to be odd. -/
theorem p2m_local_odd_ell_of_odd_three_mul (ell : ℕ)
    (hodd : Odd (3 * ell)) : Odd ell := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨ell / 2, ?_⟩
  omega





end Couret.CayleyDoublet


theorem solution : ∀ (ell : Nat),
  @Odd.{0} Nat Nat.instSemiring
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell) →
    @Odd.{0} Nat Nat.instSemiring ell := @_root_.Couret.CayleyDoublet.p2m_local_odd_ell_of_odd_three_mul

