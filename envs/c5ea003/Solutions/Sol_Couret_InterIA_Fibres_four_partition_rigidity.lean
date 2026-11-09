-- Prove2me | solution 1 for Couret.InterIA.Fibres.four_partition_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:32.382195+00:00
-- url     : https://prove2.me/submissions/37a4330d-af57-444f-beee-deacf342c320

import Definitions.Def_Couret_FourSignRigidity_4bbe2289ca60
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial











/-- Algebraic partition assembly; the seven nonvanishing premises cover every mixed flip. -/
theorem p2m_local_four_partition_rigidity (Q A B C D : ℝ[X])
    (hfour : IsCoprime Q (4 : ℝ[X]))
    (hA : ¬ Q ∣ A*(B+C+D)) (hB : ¬ Q ∣ B*(A+C+D))
    (hC : ¬ Q ∣ C*(A+B+D)) (hD : ¬ Q ∣ D*(A+B+C))
    (hAB : ¬ Q ∣ (A+B)*(C+D)) (hAC : ¬ Q ∣ (A+C)*(B+D))
    (hAD : ¬ Q ∣ (A+D)*(B+C))
    (e0 e1 e2 e3 : Bool)
    (heq : Q ∣ (A+B+C+D)^2 -
      (signed e0 A + signed e1 B + signed e2 C + signed e3 D)^2) :
    signed e0 A + signed e1 B + signed e2 C + signed e3 D = A+B+C+D ∨
    signed e0 A + signed e1 B + signed e2 C + signed e3 D = -(A+B+C+D) := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases e3
  · exact Or.inl rfl
  · exfalso
    apply hD
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hC
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hAB
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hB
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hAC
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hAD
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hA
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hA
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hAD
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hAC
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hB
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hAB
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hC
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · exfalso
    apply hD
    apply hfour.dvd_of_dvd_mul_left
    convert heq using 1; simp [signed]; ring
  · right
    simp [signed]
    ring





end Couret.InterIA.Fibres

theorem solution : ∀ (Q A B C D : @Polynomial.{0} Real Real.semiring),
  @IsCoprime.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.commSemiring.{0} Real Real.instCommSemiring) Q
      (@OfNat.ofNat.{0} (@Polynomial.{0} Real Real.semiring) (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} (@Polynomial.{0} Real Real.semiring) (nat_lit 4)
          (@Polynomial.instNatCast.{0} Real Real.semiring)
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) →
    Not
        (@Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
          (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
            (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
              (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                  (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                    (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                      (@Polynomial.commRing.{0} Real Real.commRing)))))))
          Q
          (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
            (@Polynomial.{0} Real Real.semiring)
            (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instMul.{0} Real Real.semiring)) A
            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
              (@Polynomial.{0} Real Real.semiring)
              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                (@Polynomial.{0} Real Real.semiring)
                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring)) B C)
              D))) →
      Not
          (@Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
            (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
              (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                  (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                    (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                      (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                        (@Polynomial.commRing.{0} Real Real.commRing)))))))
            Q
            (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
              (@Polynomial.{0} Real Real.semiring)
              (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instMul.{0} Real Real.semiring)) B
              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                (@Polynomial.{0} Real Real.semiring)
                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
                (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                  (@Polynomial.{0} Real Real.semiring)
                  (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring)) A C)
                D))) →
        Not
            (@Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
              (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
                (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                  (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                    (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                      (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                        (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.commRing.{0} Real Real.commRing)))))))
              Q
              (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                (@Polynomial.{0} Real Real.semiring)
                (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instMul.{0} Real Real.semiring)) C
                (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                  (@Polynomial.{0} Real Real.semiring)
                  (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
                  (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                    (@Polynomial.{0} Real Real.semiring)
                    (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring)) A
                    B)
                  D))) →
          Not
              (@Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
                (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
                  (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                    (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                      (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                        (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                          (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.commRing.{0} Real Real.commRing)))))))
                Q
                (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                  (@Polynomial.{0} Real Real.semiring)
                  (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instMul.{0} Real Real.semiring)) D
                  (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                    (@Polynomial.{0} Real Real.semiring)
                    (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
                    (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                      (@Polynomial.{0} Real Real.semiring)
                      (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
                      A B)
                    C))) →
            Not
                (@Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
                  (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
                    (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                      (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                        (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                          (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                            (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.commRing.{0} Real Real.commRing)))))))
                  Q
                  (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                    (@Polynomial.{0} Real Real.semiring)
                    (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instMul.{0} Real Real.semiring))
                    (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                      (@Polynomial.{0} Real Real.semiring)
                      (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
                      A B)
                    (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                      (@Polynomial.{0} Real Real.semiring)
                      (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
                      C D))) →
              Not
                  (@Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
                    (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
                      (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                        (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                          (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                            (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                              (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.commRing.{0} Real Real.commRing)))))))
                    Q
                    (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                      (@Polynomial.{0} Real Real.semiring)
                      (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instMul.{0} Real Real.semiring))
                      (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                        (@Polynomial.{0} Real Real.semiring)
                        (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.instAdd.{0} Real Real.semiring))
                        A C)
                      (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                        (@Polynomial.{0} Real Real.semiring)
                        (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.instAdd.{0} Real Real.semiring))
                        B D))) →
                Not
                    (@Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
                      (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
                        (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                          (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                            (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                              (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.commRing.{0} Real Real.commRing)))))))
                      Q
                      (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                        (@Polynomial.{0} Real Real.semiring)
                        (@instHMul.{0} (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.instMul.{0} Real Real.semiring))
                        (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.{0} Real Real.semiring)
                          (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.instAdd.{0} Real Real.semiring))
                          A D)
                        (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.{0} Real Real.semiring)
                          (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.instAdd.{0} Real Real.semiring))
                          B C))) →
                  ∀ (e0 e1 e2 e3 : Bool),
                    @Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
                        (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
                          (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                            (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                              (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.commRing.{0} Real Real.commRing)))))))
                        Q
                        (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.{0} Real Real.semiring)
                          (@instHSub.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.instSub.{0} Real Real.instRing))
                          (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                            (@Polynomial.{0} Real Real.semiring)
                            (@instHPow.{0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                              (@Monoid.toPow.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Semiring.toMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.semiring.{0} Real Real.semiring))))
                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.instAdd.{0} Real Real.semiring))
                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                  (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.instAdd.{0} Real Real.semiring))
                                  A B)
                                C)
                              D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                            (@Polynomial.{0} Real Real.semiring)
                            (@instHPow.{0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                              (@Monoid.toPow.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Semiring.toMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.semiring.{0} Real Real.semiring))))
                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.instAdd.{0} Real Real.semiring))
                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                  (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.instAdd.{0} Real Real.semiring))
                                  (Couret.InterIA.Fibres.signed e0 A) (Couret.InterIA.Fibres.signed e1 B))
                                (Couret.InterIA.Fibres.signed e2 C))
                              (Couret.InterIA.Fibres.signed e3 D))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                      Or
                        (@Eq.{1} (@Polynomial.{0} Real Real.semiring)
                          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.instAdd.{0} Real Real.semiring))
                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.instAdd.{0} Real Real.semiring))
                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                (Couret.InterIA.Fibres.signed e0 A) (Couret.InterIA.Fibres.signed e1 B))
                              (Couret.InterIA.Fibres.signed e2 C))
                            (Couret.InterIA.Fibres.signed e3 D))
                          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.instAdd.{0} Real Real.semiring))
                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.instAdd.{0} Real Real.semiring))
                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                A B)
                              C)
                            D))
                        (@Eq.{1} (@Polynomial.{0} Real Real.semiring)
                          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.instAdd.{0} Real Real.semiring))
                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.instAdd.{0} Real Real.semiring))
                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                (Couret.InterIA.Fibres.signed e0 A) (Couret.InterIA.Fibres.signed e1 B))
                              (Couret.InterIA.Fibres.signed e2 C))
                            (Couret.InterIA.Fibres.signed e3 D))
                          (@Neg.neg.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.instNeg.{0} Real Real.instRing)
                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.instAdd.{0} Real Real.semiring))
                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                  (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.instAdd.{0} Real Real.semiring))
                                  A B)
                                C)
                              D))) := @_root_.Couret.InterIA.Fibres.p2m_local_four_partition_rigidity

