-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Orbits.invariant_coeff_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:53.005754+00:00
-- url     : https://prove2.me/submissions/306c03d4-4f45-4556-b5dc-0ac59f358e7c

import Definitions.Def_Couret_QuotientOrbits_0c82b3d4a090
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_QuotientPeriods_cf8d74422994

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Orbits
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]





theorem p2m_local_invariant_coeff_nsmul (W : AddMonoidAlgebra ℤ G) (δ : G)
    (he : W=AddMonoidAlgebra.single δ 1*W) (x : G) (k : ℕ) :
    W.coeff (x+k • δ)=W.coeff x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul,← add_assoc,invariant_coeff_shift W δ he,ih]





end Couret.InterIA.Catalogue.Orbits

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G]
  (W : @AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) (δ : G),
  @Eq.{p2m_u_0 + 1} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) W
      (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
        (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
        (@instHMul.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
          (@AddMonoidAlgebra.instMul.{0, p2m_u_0} Int G Int.instSemiring
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))))
        (@AddMonoidAlgebra.single.{0, p2m_u_0} Int G Int.instSemiring δ
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        W) →
    ∀ (x : G) (k : Nat),
      @Eq.{1} Int
        (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
          (@Finsupp.{p2m_u_0, 0} G Int
            (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
          G (fun x => Int)
          (@Finsupp.instFunLike.{p2m_u_0, 0} G Int
            (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
          (@AddMonoidAlgebra.coeff.{0, p2m_u_0} Int G Int.instSemiring W)
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            x
            (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat G G
              (@instHSMul.{0, p2m_u_0} Nat G
                (@AddMonoid.toNSMul.{p2m_u_0} G
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
              k δ)))
        (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
          (@Finsupp.{p2m_u_0, 0} G Int
            (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
          G (fun x => Int)
          (@Finsupp.instFunLike.{p2m_u_0, 0} G Int
            (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
          (@AddMonoidAlgebra.coeff.{0, p2m_u_0} Int G Int.instSemiring W) x) := @_root_.Couret.InterIA.Catalogue.Orbits.p2m_local_invariant_coeff_nsmul

