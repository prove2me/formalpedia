-- Prove2me | solution 1 for Couret.Strobo2Tors.orderedRep_three
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:59:43.071331+00:00
-- url     : https://prove2.me/submissions/f96ab910-cf7d-4746-8470-1484b504a1ad

import Definitions.Def_Couret_CrossedOrderThree_8ba7af1c9194
import Mathlib
import Definitions.Def_Couret_CrossedOrderThree_8ba7af1c9194

/-!
Exact expansion of a labelled triple convolution square.
This connects SameSquare to all nine ordered sums, including diagonals.
No assertion of complete classification or uniqueness is made here.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Explicit ordered representation formula for a three-element support. -/
theorem p2m_local_orderedRep_three (a c b w : G)
    (hac : a ≠ c) (hab : a ≠ b) (hcb : c ≠ b) :
    orderedRep ({a, c, b} : Finset G) w =
      (if a + a = w then 1 else 0) +
      (if c + c = w then 1 else 0) +
      (if b + b = w then 1 else 0) +
      2 * (if a + c = w then 1 else 0) +
      2 * (if a + b = w then 1 else 0) +
      2 * (if c + b = w then 1 else 0) := by
  classical
  have ha_mem : a ∉ ({c, b} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hac, hab⟩
  have hc_mem : c ∉ ({b} : Finset G) := by
    simpa only [Finset.mem_singleton] using hcb
  unfold orderedRep
  rw [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
  simp only [Finset.sum_insert ha_mem, Finset.sum_insert hc_mem,
    Finset.sum_singleton, two_mul, add_comm, add_left_comm, add_assoc]

end Couret.Strobo2Tors

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [Fintype.{p2m_u_0} G] [inst_2 : DecidableEq.{p2m_u_0 + 1} G]
  (a c b w : G),
  @Ne.{p2m_u_0 + 1} G a c →
    @Ne.{p2m_u_0 + 1} G a b →
      @Ne.{p2m_u_0 + 1} G c b →
        @Eq.{1} Nat
          (@Couret.Strobo2Tors.orderedRep.{p2m_u_0} G inst inst_2
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_2) a
              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_2) c
                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G) b)))
            w)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@ite.{1} Nat
                      (@Eq.{p2m_u_0 + 1} G
                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHAdd.{p2m_u_0} G
                            (@AddCommMagma.toAdd.{p2m_u_0} G
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                          a a)
                        w)
                      (inst_2
                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHAdd.{p2m_u_0} G
                            (@AddCommMagma.toAdd.{p2m_u_0} G
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                          a a)
                        w)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@ite.{1} Nat
                      (@Eq.{p2m_u_0 + 1} G
                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHAdd.{p2m_u_0} G
                            (@AddCommMagma.toAdd.{p2m_u_0} G
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                          c c)
                        w)
                      (inst_2
                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHAdd.{p2m_u_0} G
                            (@AddCommMagma.toAdd.{p2m_u_0} G
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                          c c)
                        w)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (@ite.{1} Nat
                    (@Eq.{p2m_u_0 + 1} G
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        b b)
                      w)
                    (inst_2
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        b b)
                      w)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@ite.{1} Nat
                    (@Eq.{p2m_u_0 + 1} G
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        a c)
                      w)
                    (inst_2
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        a c)
                      w)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@ite.{1} Nat
                  (@Eq.{p2m_u_0 + 1} G
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      a b)
                    w)
                  (inst_2
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      a b)
                    w)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@ite.{1} Nat
                (@Eq.{p2m_u_0 + 1} G
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    c b)
                  w)
                (inst_2
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    c b)
                  w)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := @_root_.Couret.Strobo2Tors.p2m_local_orderedRep_three

