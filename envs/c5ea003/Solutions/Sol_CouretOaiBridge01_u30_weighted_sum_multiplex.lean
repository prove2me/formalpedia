-- Prove2me | solution 1 for CouretOaiBridge01.u30_weighted_sum_multiplex
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:03:00.149364+00:00
-- url     : https://prove2.me/submissions/e6299d2e-a769-4145-97bf-5bd411448faa

import Definitions.Def_Couret_BRIDGE01_B0_DirichletMultiplexer_d0ed5832539d
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Theorems.Thm_CouretOaiBridge01_u30_dirichlet_fourier_inversion
import Definitions.Def_Couret_BRIDGE01_B0_DirichletMultiplexer_d0ed5832539d
import Mathlib.Tactic

open scoped BigOperators

namespace CouretOaiBridge01

noncomputable section

/--
B1: exact finite weighted-sum multiplexing identity.

A weight on U(30) does not create a new analytic channel: every finite weighted sum
is exactly a linear combination of the Dirichlet-character channels, with coefficients
given by the finite Fourier transform of the weight.
-/
theorem p2m_local_u30_weighted_sum_multiplex
    {R I : Type*} [CommRing R] [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent U30)]
    [Fintype I]
    (w : U30 → R) (c : I → R) (r : I → U30) :
    ((30 : ℕ).totient : R) * (∑ i : I, c i * w (r i)) =
      ∑ χ : DirichletCharacter R 30,
        u30FourierCoeff w χ * (∑ i : I, c i * χ (r i : ZMod 30)) := by
  calc
    ((30 : ℕ).totient : R) * (∑ i : I, c i * w (r i))
        = ∑ i : I, c i * (((30 : ℕ).totient : R) * w (r i)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = ∑ i : I, c i *
          (∑ χ : DirichletCharacter R 30,
            u30FourierCoeff w χ * χ (r i : ZMod 30)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [u30_dirichlet_fourier_inversion]
    _ = ∑ χ : DirichletCharacter R 30,
          u30FourierCoeff w χ * (∑ i : I, c i * χ (r i : ZMod 30)) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro χ hχ
          apply Finset.sum_congr rfl
          intro i hi
          ring

end

end CouretOaiBridge01

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {R : Type p2m_u_0} {I : Type p2m_u_1} [inst : CommRing.{p2m_u_0} R]
  [inst_1 : @IsDomain.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))]
  [@HasEnoughRootsOfUnity.{p2m_u_0} R (@CommRing.toCommMonoid.{p2m_u_0} R inst)
      (@Monoid.exponent.{0} CouretOaiBridge01.U30
        (@Units.instMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
          (@Semiring.toMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (@CommSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
              (@CommRing.toCommSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))))]
  [inst_3 : Fintype.{p2m_u_1} I] (w : CouretOaiBridge01.U30 → R) (c : I → R) (r : I → CouretOaiBridge01.U30),
  @Eq.{p2m_u_0 + 1} R
    (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
      (@instHMul.{p2m_u_0} R
        (@Distrib.toMul.{p2m_u_0} R
          (@instDistribOfSemiring.{p2m_u_0} R
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
      (@Nat.cast.{p2m_u_0} R
        (@AddMonoidWithOne.toNatCast.{p2m_u_0} R
          (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R
            (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))
        (Nat.totient (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
      (@Finset.sum.{p2m_u_1, p2m_u_0} I R
        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} R
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0} R
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0} R
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0} R
                (@CommRing.toNonUnitalCommRing.{p2m_u_0} R inst)))))
        (@Finset.univ.{p2m_u_1} I inst_3) fun i =>
        @HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
          (@instHMul.{p2m_u_0} R
            (@Distrib.toMul.{p2m_u_0} R
              (@instDistribOfSemiring.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
          (c i) (w (r i))))
    (@Finset.sum.{p2m_u_0, p2m_u_0}
      (@DirichletCharacter.{p2m_u_0} R
        (@CommSemiring.toCommMonoidWithZero.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
        (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
      R
      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} R
        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0} R
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0} R
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0} R
              (@CommRing.toNonUnitalCommRing.{p2m_u_0} R inst)))))
      (@Finset.univ.{p2m_u_0}
        (@DirichletCharacter.{p2m_u_0} R
          (@CommSemiring.toCommMonoidWithZero.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
        (@DirichletCharacter.fintype.{p2m_u_0} R inst inst_1
          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
      fun χ =>
      @HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
        (@instHMul.{p2m_u_0} R
          (@Distrib.toMul.{p2m_u_0} R
            (@instDistribOfSemiring.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
        (@CouretOaiBridge01.u30FourierCoeff.{p2m_u_0} R inst w χ)
        (@Finset.sum.{p2m_u_1, p2m_u_0} I R
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} R
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0} R
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0} R
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0} R
                  (@CommRing.toNonUnitalCommRing.{p2m_u_0} R inst)))))
          (@Finset.univ.{p2m_u_1} I inst_3) fun i =>
          @HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHMul.{p2m_u_0} R
              (@Distrib.toMul.{p2m_u_0} R
                (@instDistribOfSemiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
            (c i)
            (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
              (@DirichletCharacter.{p2m_u_0} R
                (@CommSemiring.toCommMonoidWithZero.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) (fun x => R)
              (@MulChar.instFunLike.{0, p2m_u_0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                (@CommRing.toCommMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                R (@CommSemiring.toCommMonoidWithZero.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              χ
              (@Units.val.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                (@Semiring.toMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                  (@CommSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                    (@CommRing.toCommSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                (r i))))) := @_root_.CouretOaiBridge01.p2m_local_u30_weighted_sum_multiplex

