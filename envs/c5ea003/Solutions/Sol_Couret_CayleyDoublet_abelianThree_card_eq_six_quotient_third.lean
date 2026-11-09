-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_card_eq_six_quotient_third
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:30:40.512507+00:00
-- url     : https://prove2.me/submissions/28c18c4a-98f9-4d06-95f7-14a40279ac80

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f

/-!
COU-20: the first differing characteristic-polynomial coefficient.

The original spectral equivalence and first-trace certificates are imported
unchanged. We reuse the previously proved finite Newton prefix identities,
the generic single-matrix Newton theorem, and the canonical odd quotient
return. All statements refer to the actual rational directed adjacency
matrices (including their loops).

The numerical absolute-gap formula remains a documented mathematical
corollary, not a claim of formalization in this file.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]








/-- A nonzero half-turn generates a subgroup of cardinal 2. Combined
with odd quotient size 3*k this gives the exact ambient size 6*k. -/
theorem p2m_local_abelianThree_card_eq_six_quotient_third
    (h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (k : ℕ)
    (hsize : Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * k) :
    Fintype.card G = 6 * k := by
  have htwo : addOrderOf h = 2 := by
    have hsmul : (2 : ℕ) • h = 0 := by simpa [two_nsmul] using hhalf
    have hdiv : addOrderOf h ∣ 2 :=
      (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hsmul
    have hnotone : addOrderOf h ≠ 1 := by
      intro horder
      have hz := addOrderOf_nsmul_eq_zero h
      rw [horder] at hz
      exact hne (by simpa using hz)
    have hle : addOrderOf h ≤ 2 :=
      Nat.le_of_dvd (by decide : 0 < 2) hdiv
    have hnonzero : addOrderOf h ≠ 0 := by
      intro hz
      simp [hz] at hdiv
    omega
  have hsub : Nat.card (AddSubgroup.zmultiples h) = 2 := by
    simpa only [Nat.card_zmultiples] using htwo
  calc
    Fintype.card G = Nat.card G := Nat.card_eq_fintype_card.symm
    _ = Nat.card (G ⧸ AddSubgroup.zmultiples h) *
        Nat.card (AddSubgroup.zmultiples h) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = 6 * k := by rw [hsub, hsize]; omega




end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G] [inst_2 : Fintype.{p2m_u_0} G]
  (h : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        h h)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G h
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      ∀ (k : Nat),
        @Eq.{1} Nat
            (Nat.card.{p2m_u_0}
              (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k) →
          @Eq.{1} Nat (@Fintype.card.{p2m_u_0} G inst_2)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) k) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_card_eq_six_quotient_third

