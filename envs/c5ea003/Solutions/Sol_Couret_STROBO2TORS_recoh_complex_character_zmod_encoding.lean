-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_complex_character_zmod_encoding
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:02.899115+00:00
-- url     : https://prove2.me/submissions/29b986bb-0126-46a1-a5c0-87241635efc9

import Aesop
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Choose

set_option autoImplicit false

/-!
RECOH: character restrictions provide their own finite-field encodings.

Every complex additive character on a group annihilated by n factors
through the standard character of ZMod n. The binary and ternary
specializations discharge the compatibility assumptions of the existing
short-bank collision theorem. No primary character extension or upper
bound is assumed here.
-/

namespace Couret.STROBO2TORS

/-- Every complex n-th root is a value of the standard ZMod character. -/
theorem recoh_exists_stdAddChar_eq_of_pow_eq_one
    (n : ℕ) [NeZero n] (z : ℂ) (hz : z ^ n = 1) :
    ∃ a : ZMod n, ZMod.stdAddChar a = z := by
  obtain ⟨a, ha⟩ :=
    surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar n
      (rootsOfUnity.mkOfPowEq z hz)
  refine ⟨a, ?_⟩
  have hv := congrArg
    (fun w : rootsOfUnity n ℂ => ((w : ℂˣ) : ℂ)) ha
  simpa only [Function.comp_apply, rootsOfUnityCircleEquiv_apply,
    ZMod.rootsOfUnityAddChar_val, rootsOfUnity.coe_mkOfPowEq,
    ← ZMod.stdAddChar_apply] using hv

/-- Restriction to an exponent-n group admits an additive ZMod n encoding.
The full character value is recovered from the encoding. -/
theorem p2m_local_recoh_complex_character_zmod_encoding
    {A : Type*} [AddCommGroup A]
    (n : ℕ) [NeZero n] (hexp : ∀ a : A, n • a = 0)
    (chi : AddChar A ℂ) :
    ∃ bits : A →+ ZMod n, ∀ a : A,
      ZMod.stdAddChar (bits a) = chi a := by
  classical
  have hexists : ∀ a : A, ∃ b : ZMod n,
      ZMod.stdAddChar b = chi a := by
    intro a
    apply recoh_exists_stdAddChar_eq_of_pow_eq_one n (chi a)
    rw [← chi.map_nsmul_eq_pow, hexp a, chi.map_zero_eq_one]
  choose f hf using hexists
  let bits : A →+ ZMod n :=
    { toFun := f
      map_zero' := by
        apply ZMod.injective_stdAddChar
        rw [hf, chi.map_zero_eq_one, AddChar.map_zero_eq_one]
      map_add' := by
        intro a b
        apply ZMod.injective_stdAddChar
        rw [hf, (ZMod.stdAddChar (N := n)).map_add_eq_mul, hf, hf,
          chi.map_add_eq_mul] }
  exact ⟨bits, hf⟩





variable {G : Type*} [AddCommGroup G] [DecidableEq G]



end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {A : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} A] (n : Nat)
  [inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n],
  (∀ (a : A),
      @Eq.{p2m_u_0 + 1} A
        (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat A A
          (@instHSMul.{0, p2m_u_0} Nat A
            (@AddMonoid.toNSMul.{p2m_u_0} A
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
          n a)
        (@OfNat.ofNat.{p2m_u_0} A (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} A
            (@NegZeroClass.toZero.{p2m_u_0} A
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} A
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} A
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} A
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} A inst)))))))) →
    ∀
      (chi :
        @AddChar.{p2m_u_0, 0} A
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
            (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))
          Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
      @Exists.{p2m_u_0 + 1}
        (@AddMonoidHom.{p2m_u_0, 0} A (ZMod n)
          (@AddZeroClass.toAddZero.{p2m_u_0} A
            (@AddMonoid.toAddZeroClass.{p2m_u_0} A
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
          (@AddZeroClass.toAddZero.{0} (ZMod n)
            (@AddMonoid.toAddZeroClass.{0} (ZMod n)
              (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                  (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))))))
        fun bits =>
        ∀ (a : A),
          @Eq.{1} Complex
            (@DFunLike.coe.{1, 1, 1}
              (@AddChar.{0, 0} (ZMod n)
                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                    (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
              (ZMod n) (fun x => Complex)
              (@AddChar.instFunLike.{0, 0} (ZMod n) Complex
                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                    (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
                (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
              (@ZMod.stdAddChar n inst_1)
              (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                (@AddMonoidHom.{p2m_u_0, 0} A (ZMod n)
                  (@AddZeroClass.toAddZero.{p2m_u_0} A
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
                  (@AddZeroClass.toAddZero.{0} (ZMod n)
                    (@AddMonoid.toAddZeroClass.{0} (ZMod n)
                      (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                          (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))))))
                A (fun x => ZMod n)
                (@AddMonoidHom.instFunLike.{p2m_u_0, 0} A (ZMod n)
                  (@AddZeroClass.toAddZero.{p2m_u_0} A
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
                  (@AddZeroClass.toAddZero.{0} (ZMod n)
                    (@AddMonoid.toAddZeroClass.{0} (ZMod n)
                      (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
                          (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))))))
                bits a))
            (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
              (@AddChar.{p2m_u_0, 0} A
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))
                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
              A (fun x => Complex)
              (@AddChar.instFunLike.{p2m_u_0, 0} A Complex
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))
                (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
              chi a) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_complex_character_zmod_encoding

