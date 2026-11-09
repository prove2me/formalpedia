-- Prove2me | solution 1 for Couret.CayleyCanonical.canonical_of_odd_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:59:17.820905+00:00
-- url     : https://prove2.me/submissions/6b2ae75a-dfaf-473c-9107-7186e6756993

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyCanonical_canonical_of_natural_coordinate
import Theorems.Thm_Couret_CayleyNecessity_odd_multiple_or_neg_of_cyclic
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





/-- In an odd cyclic group, any element of exact order 3 is one of
the two nonzero third-period multiples of the specified generator.
Unlike an abstract existential odd witness, this identifies the
*canonical* exponent ell, independent of the element delta. -/
theorem p2m_local_canonical_of_odd_cyclic
    {Q : Type*} [AddCommGroup Q] [Finite Q]
    (alpha delta : Q) (ell : ℕ)
    (hgen : AddSubgroup.zmultiples alpha = ⊤)
    (hodd : Odd (Nat.card Q))
    (hell : 0 < ell)
    (hord : addOrderOf alpha = 3 * ell)
    (hdorder : addOrderOf delta = 3) :
    ell • alpha = delta ∨ ell • alpha = -delta := by
  have hthree : (3 : ℕ) • delta = 0 := by
    simpa [hdorder] using addOrderOf_nsmul_eq_zero delta
  have hne : delta ≠ 0 := by
    intro hz
    have ho : addOrderOf delta = 1 := by simp [hz]
    omega
  obtain ⟨n, _, hn | hn⟩ :=
    Couret.CayleyNecessity.odd_multiple_or_neg_of_cyclic
      alpha delta hgen hodd
  · exact canonical_of_natural_coordinate alpha delta ell n
      hell hord hn hthree hne
  · have hthreeNeg : (3 : ℕ) • (-delta) = 0 := by
      calc
        (3 : ℕ) • (-delta) = -((3 : ℕ) • delta) := by
          simp only [three_nsmul]
          abel
        _ = 0 := by rw [hthree]; simp
    have hneNeg : -delta ≠ 0 := neg_ne_zero.mpr hne
    rcases canonical_of_natural_coordinate alpha (-delta) ell n
        hell hord hn hthreeNeg hneNeg with hneg | hpos
    · exact Or.inr hneg
    · exact Or.inl (by simpa only [neg_neg] using hpos)

end Couret.CayleyCanonical

namespace Couret.CayleyDoublet

open Couret.CayleyCanonical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]










end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {Q : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} Q] [Finite.{p2m_u_0 + 1} Q] (alpha delta : Q) (ell : Nat),
  @Eq.{p2m_u_0 + 1} (@AddSubgroup.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst))
      (@AddSubgroup.zmultiples.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst) alpha)
      (@Top.top.{p2m_u_0} (@AddSubgroup.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst))
        (@AddSubgroup.instTop.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst))) →
    @Odd.{0} Nat Nat.instSemiring (Nat.card.{p2m_u_0} Q) →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ell →
        @Eq.{1} Nat
            (@addOrderOf.{p2m_u_0} Q
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))
              alpha)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell) →
          @Eq.{1} Nat
              (@addOrderOf.{p2m_u_0} Q
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))
                delta)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            Or
              (@Eq.{p2m_u_0 + 1} Q
                (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
                  (@instHSMul.{0, p2m_u_0} Nat Q
                    (@AddMonoid.toNSMul.{p2m_u_0} Q
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
                  ell alpha)
                delta)
              (@Eq.{p2m_u_0 + 1} Q
                (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
                  (@instHSMul.{0, p2m_u_0} Nat Q
                    (@AddMonoid.toNSMul.{p2m_u_0} Q
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
                  ell alpha)
                (@Neg.neg.{p2m_u_0} Q
                  (@NegZeroClass.toNeg.{p2m_u_0} Q
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} Q
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} Q
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} Q
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} Q inst)))))
                  delta)) := @_root_.Couret.CayleyCanonical.p2m_local_canonical_of_odd_cyclic

