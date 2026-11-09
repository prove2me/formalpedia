-- Prove2me | solution 1 for CouretOaiBridge01.u30_dirichlet_fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:46:48.611001+00:00
-- url     : https://prove2.me/submissions/f69d0744-a3c8-47eb-9cbd-0d0b391fc355

import Definitions.Def_Couret_BRIDGE01_B0_DirichletMultiplexer_d0ed5832539d
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Definitions.Def_Couret_BRIDGE01_A1_U30KernelInverse_5560f1024274
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic

open scoped BigOperators

namespace CouretOaiBridge01

noncomputable section



/--
B0: exact finite Dirichlet-character multiplexing/inversion on U(30).

The result is stated over any integral domain with enough roots of unity for U(30).
It contains no L-function, convergence, or analytic-continuation input.
-/
theorem p2m_local_u30_dirichlet_fourier_inversion
    {R : Type*} [CommRing R] [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent U30)]
    (w : U30 → R) (a : U30) :
    ((30 : ℕ).totient : R) * w a =
      ∑ χ : DirichletCharacter R 30, u30FourierCoeff w χ * χ (a : ZMod 30) := by
  symm
  simp only [u30FourierCoeff]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    ∑ b : U30, ∑ χ : DirichletCharacter R 30,
        w b * χ ((b : ZMod 30)⁻¹) * χ (a : ZMod 30)
        = ∑ b : U30, w b *
            (∑ χ : DirichletCharacter R 30,
              χ ((b : ZMod 30)⁻¹) * χ (a : ZMod 30)) := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro χ hχ
              ring
    _ = ∑ b : U30, w b *
          (if (b : ZMod 30) = (a : ZMod 30) then ((30 : ℕ).totient : R) else 0) := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [DirichletCharacter.sum_char_inv_mul_char_eq]
            exact Units.isUnit b
    _ = w a * ((30 : ℕ).totient : R) := by
          rw [Finset.sum_eq_single a]
          · simp
          · intro b hb hba
            have hcoe : (b : ZMod 30) ≠ (a : ZMod 30) := by
              intro h
              apply hba
              exact Units.ext h
            simp [hcoe]
          · simp
    _ = ((30 : ℕ).totient : R) * w a := by
          rw [mul_comm]

end

end CouretOaiBridge01

universe p2m_u_0
theorem solution : ∀ {R : Type p2m_u_0} [inst : CommRing.{p2m_u_0} R]
  [inst_1 : @IsDomain.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))]
  [@HasEnoughRootsOfUnity.{p2m_u_0} R (@CommRing.toCommMonoid.{p2m_u_0} R inst)
      (@Monoid.exponent.{0} CouretOaiBridge01.U30
        (@Units.instMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
          (@Semiring.toMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (@CommSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
              (@CommRing.toCommSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))))]
  (w : CouretOaiBridge01.U30 → R) (a : CouretOaiBridge01.U30),
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
      (w a))
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
            a))) := @_root_.CouretOaiBridge01.p2m_local_u30_dirichlet_fourier_inversion

