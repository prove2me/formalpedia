-- Prove2me | solution 1 for Couret.InterIA.C4m.encoded_squares_equal
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:13.371292+00:00
-- url     : https://prove2.me/submissions/a5633ca4-92a3-4ae3-96a2-52097b2fc924

import Aesop
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_C4m_entries_distinct
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

noncomputable section

namespace Couret.InterIA.C4m
open Finset
open Couret.STROBO2TORS

/-!
Parametric, labelled ordered-square collisions in C_(4m), m >= 2.
The family originates in the coordinator's post-primary derivation in private
PR #333. This formalization makes no claim of novelty or provider autonomy.
`orderedSquare` and `translateSupport` are imported unchanged from STROBO,
the core used by the RECOH conditional orbit bridge. See PROVENANCE.json.
-/





/-- The factorization is a ring identity, before imposing any cyclic relation. -/
theorem polynomial_identity {R : Type*} [CommRing R] (X Y : R) :
    (1 + X + Y + X * Y^2)^2 - (1 + Y + X*Y + X*Y^3)^2 =
      X * (1 - Y^4) * (2 + X + X*Y^2) := by ring

theorem square_eq_of_fourth_power {R : Type*} [CommRing R]
    (X Y : R) (hY : Y^4 = 1) :
    (1 + X + Y + X * Y^2)^2 = (1 + Y + X*Y + X*Y^3)^2 := by
  apply sub_eq_zero.mp
  rw [polynomial_identity, hY]
  ring








variable {G : Type*} [AddCommGroup G] [DecidableEq G]





theorem encode_four (a b c d : G) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    encode ({a,b,c,d} : Finset G) = AddMonoidAlgebra.single a 1 +
      AddMonoidAlgebra.single b 1 + AddMonoidAlgebra.single c 1 +
      AddMonoidAlgebra.single d 1 := by
  simp [encode, hab, hac, had, hbc, hbd, hcd, add_assoc]



/-- Equality in the integral group algebra, before extracting each coefficient. -/
theorem p2m_local_encoded_squares_equal (m : ℕ) (hm : 2 ≤ m) :
    encode (T m) ^ 2 = encode (U m) ^ 2 := by
  obtain ⟨h01,h0m,h0t,h1m,h1t,hmt,h0v,h0u,hmv,hmu,hvu⟩ := entries_distinct m hm
  let X : AddMonoidAlgebra ℤ (ZMod (4*m)) := AddMonoidAlgebra.single 1 1
  let Y : AddMonoidAlgebra ℤ (ZMod (4*m)) := AddMonoidAlgebra.single m 1
  have hz : (4 : ZMod (4*m)) * m = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (ZMod.natCast_self (4*m))
  have hY : Y^4 = 1 := by
    simp [Y, AddMonoidAlgebra.single_pow, nsmul_eq_mul, hz, AddMonoidAlgebra.one_def]
  have hT : encode (T m) = 1 + X + Y + X*Y^2 := by
    rw [T, encode_four 0 1 _ _ h01 h0m h0t h1m h1t hmt]
    simp [X,Y,AddMonoidAlgebra.one_def,AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_mul_single,nsmul_eq_mul,add_comm,add_assoc]
  have hU : encode (U m) = 1 + Y + X*Y + X*Y^3 := by
    rw [U, encode_four 0 _ _ _ h0m h0v h0u hmv hmu hvu]
    simp [X,Y,AddMonoidAlgebra.one_def,AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_mul_single,nsmul_eq_mul,add_comm,add_assoc]
  rw [hT,hU]
  exact square_eq_of_fourth_power X Y hY














end Couret.InterIA.C4m

theorem solution : ∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    @Eq.{1}
      (@AddMonoidAlgebra.{0, 0} Int
        (ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
        Int.instSemiring)
      (@HPow.hPow.{0, 0, 0}
        (@AddMonoidAlgebra.{0, 0} Int
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
          Int.instSemiring)
        Nat
        (@AddMonoidAlgebra.{0, 0} Int
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
          Int.instSemiring)
        (@instHPow.{0, 0}
          (@AddMonoidAlgebra.{0, 0} Int
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
            Int.instSemiring)
          Nat
          (@Monoid.toPow.{0}
            (@AddMonoidAlgebra.{0, 0} Int
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
              Int.instSemiring)
            (@Semiring.toMonoid.{0}
              (@AddMonoidAlgebra.{0, 0} Int
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                Int.instSemiring)
              (@AddMonoidAlgebra.semiring.{0, 0} Int
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                Int.instSemiring
                (@AddMonoidWithOne.toAddMonoid.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                    (@Ring.toAddGroupWithOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                      (@CommRing.toRing.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                        (ZMod.commRing
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))))))))))
        (@Couret.InterIA.C4m.encode.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
          (Couret.InterIA.C4m.T m))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HPow.hPow.{0, 0, 0}
        (@AddMonoidAlgebra.{0, 0} Int
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
          Int.instSemiring)
        Nat
        (@AddMonoidAlgebra.{0, 0} Int
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
          Int.instSemiring)
        (@instHPow.{0, 0}
          (@AddMonoidAlgebra.{0, 0} Int
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
            Int.instSemiring)
          Nat
          (@Monoid.toPow.{0}
            (@AddMonoidAlgebra.{0, 0} Int
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
              Int.instSemiring)
            (@Semiring.toMonoid.{0}
              (@AddMonoidAlgebra.{0, 0} Int
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                Int.instSemiring)
              (@AddMonoidAlgebra.semiring.{0, 0} Int
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                Int.instSemiring
                (@AddMonoidWithOne.toAddMonoid.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                    (@Ring.toAddGroupWithOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                      (@CommRing.toRing.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                        (ZMod.commRing
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))))))))))
        (@Couret.InterIA.C4m.encode.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
          (Couret.InterIA.C4m.U m))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Couret.InterIA.C4m.p2m_local_encoded_squares_equal

