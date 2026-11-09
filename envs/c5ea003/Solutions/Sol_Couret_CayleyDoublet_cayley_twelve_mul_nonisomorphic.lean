-- Prove2me | solution 1 for Couret.CayleyDoublet.cayley_twelve_mul_nonisomorphic
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:50:23.488851+00:00
-- url     : https://prove2.me/submissions/126bdba2-0361-43e1-85ad-4853b3163bc6

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_noIso_of_two_colours
import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1

set_option autoImplicit false

/-!
CAYLEY-TWO-COLOUR-ZMOD — arithmetic specialization, 2026-10-14.

This candidate closes the concrete modular arithmetic premises of the
already compiled, conditional noIso_of_two_colours theorem.

Status: NEW CANDIDATE. Do not report as compiled without the
cayley-two-colour-family-lean workflow passing on its exact commit SHA.
Only directed graph nonisomorphism is intended; no academic priority.
-/

namespace Couret.CayleyDoublet

/-- Natural casts into ZMod n are injective on the interval [0,n).
We use this rather than assuming any cancellation of modular products. -/
private theorem distinct_casts_below
    (n x y : ℕ) (hx : x < n) (hy : y < n) (hxy : x ≠ y) :
    (x : ZMod n) ≠ (y : ZMod n) := by
  intro hc
  apply hxy
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using hv

/-- For all positive r, the two explicit directed Cayley graphs on
ZMod (12*r) are non-isomorphic. The edge relation is defined exactly
by the respective triple of increment residues.

This theorem uses only the compiled algebraic bridge plus modular
inequalities proved below, without assuming an affine isomorphism. -/
theorem p2m_local_cayley_twelve_mul_nonisomorphic
    (r : ℕ) (hr : 0 < r)
    (f : ZMod (12 * r) ≃ ZMod (12 * r))
    (hf : ∀ x y : ZMod (12 * r),
      CayleyArc (TripleSupport (1 : ZMod (12 * r))
        ((1 + 2 * r : ℕ) : ZMod (12 * r))
        ((6 * r : ℕ) : ZMod (12 * r))) x y ↔
      CayleyArc (TripleSupport (1 : ZMod (12 * r))
        ((1 + 4 * r : ℕ) : ZMod (12 * r))
        ((6 * r : ℕ) : ZMod (12 * r))) (f x) (f y)) :
    False := by
  let G := ZMod (12 * r)
  let a : G := 1
  let b : G := ((1 + 2 * r : ℕ) : G)
  let c : G := ((1 + 4 * r : ℕ) : G)
  let h : G := ((6 * r : ℕ) : G)

  have hhalf : h + h = 0 := by
    change ((6 * r : ℕ) : G) + ((6 * r : ℕ) : G) = 0
    calc
      _ = ((12 * r : ℕ) : G) := by
        have hn : 6 * r + 6 * r = 12 * r := by omega
        simpa only [Nat.cast_add] using
          (congrArg (fun t : ℕ => (t : G)) hn)
      _ = 0 := ZMod.natCast_self (12 * r)

  have hne : h ≠ 0 := by
    change ((6 * r : ℕ) : G) ≠ (0 : G)
    simpa only [Nat.cast_zero, Nat.cast_one] using
      (distinct_casts_below (12 * r) (6 * r) 0
      (by omega) (by omega) (by omega))

  have hab : a ≠ b := by
    change (1 : G) ≠ ((1 + 2 * r : ℕ) : G)
    simpa only [Nat.cast_zero, Nat.cast_one] using
      (distinct_casts_below (12 * r) 1 (1 + 2 * r)
      (by omega) (by omega) (by omega))

  have hbph : b + h = ((1 + 8 * r : ℕ) : G) := by
    dsimp [b, h]
    have hn : 1 + 2 * r + 6 * r = 1 + 8 * r := by omega
    simpa only [Nat.cast_add] using
      (congrArg (fun t : ℕ => (t : G)) hn)
  have habh : a ≠ b + h := by
    rw [hbph]
    change (1 : G) ≠ ((1 + 8 * r : ℕ) : G)
    simpa only [Nat.cast_zero, Nat.cast_one] using
      (distinct_casts_below (12 * r) 1 (1 + 8 * r)
      (by omega) (by omega) (by omega))

  have hac : a ≠ c := by
    change (1 : G) ≠ ((1 + 4 * r : ℕ) : G)
    simpa only [Nat.cast_zero, Nat.cast_one] using
      (distinct_casts_below (12 * r) 1 (1 + 4 * r)
      (by omega) (by omega) (by omega))

  have hcph : c + h = ((1 + 10 * r : ℕ) : G) := by
    dsimp [c, h]
    have hn : 1 + 4 * r + 6 * r = 1 + 10 * r := by omega
    simpa only [Nat.cast_add] using
      (congrArg (fun t : ℕ => (t : G)) hn)
  have hach : a ≠ c + h := by
    rw [hcph]
    change (1 : G) ≠ ((1 + 10 * r : ℕ) : G)
    simpa only [Nat.cast_zero, Nat.cast_one] using
      (distinct_casts_below (12 * r) 1 (1 + 10 * r)
      (by omega) (by omega) (by omega))

  have hbc : b ≠ c := by
    change ((1 + 2 * r : ℕ) : G) ≠ ((1 + 4 * r : ℕ) : G)
    simpa only [Nat.cast_zero, Nat.cast_one] using
      (distinct_casts_below (12 * r) (1 + 2 * r) (1 + 4 * r)
      (by omega) (by omega) (by omega))

  have hbch : b ≠ c + h := by
    rw [hcph]
    change ((1 + 2 * r : ℕ) : G) ≠ ((1 + 10 * r : ℕ) : G)
    simpa only [Nat.cast_zero, Nat.cast_one] using
      (distinct_casts_below (12 * r) (1 + 2 * r) (1 + 10 * r)
      (by omega) (by omega) (by omega))

  have hthreeT :
      (a - c) + (a - c) + (a - c) = 0 ∨
      (a - c) + (a - c) + (a - c) = h := by
    left
    change
      ((1 : G) - ((1 + 4 * r : ℕ) : G)) +
      ((1 : G) - ((1 + 4 * r : ℕ) : G)) +
      ((1 : G) - ((1 + 4 * r : ℕ) : G)) = 0
    have hn : 4 * r + 4 * r + 4 * r = 12 * r := by omega
    have hcast :
        ((4 * r : ℕ) : G) + ((4 * r : ℕ) : G) + ((4 * r : ℕ) : G) =
          ((12 * r : ℕ) : G) := by
      simpa only [Nat.cast_add] using
        (congrArg (fun t : ℕ => (t : G)) hn)
    calc
      _ = -(((4 * r : ℕ) : G) + ((4 * r : ℕ) : G) +
            ((4 * r : ℕ) : G)) := by
        simp only [Nat.cast_add, Nat.cast_one]
        abel
      _ = -((12 * r : ℕ) : G) := by rw [hcast]
      _ = 0 := by rw [ZMod.natCast_self]; simp

  have hbk : b = (1 + 2 * r) • a := by
    dsimp [a, b]
    simp

  exact noIso_of_two_colours a b c h hhalf hne
    hab habh hac hach hthreeT (1 + 2 * r) hbk hbc hbch f hf


end Couret.CayleyDoublet

theorem solution : ∀ (r : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
    ∀
      (f :
        Equiv.{1, 1}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))),
      (∀
          (x y :
            ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r)),
          Iff
            (@Couret.CayleyDoublet.CayleyArc.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
              (@LieRing.toAddCommGroup.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (@LieRing.ofAssociativeRing.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@CommRing.toRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r)))))
              (@Couret.CayleyDoublet.TripleSupport.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (@LieRing.toAddCommGroup.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@LieRing.ofAssociativeRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (@CommRing.toRing.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                      (ZMod.commRing
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r)))))
                (ZMod.decidableEq
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (@OfNat.ofNat.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (nat_lit 1)
                  (@One.toOfNat1.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (@AddMonoidWithOne.toOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                          (@CommRing.toRing.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))))))))
                (@Nat.cast.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@AddMonoidWithOne.toNatCast.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                      (@Ring.toAddGroupWithOne.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                        (@CommRing.toRing.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                          (ZMod.commRing
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
                (@Nat.cast.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@AddMonoidWithOne.toNatCast.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                      (@Ring.toAddGroupWithOne.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                        (@CommRing.toRing.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                          (ZMod.commRing
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) r)))
              x y)
            (@Couret.CayleyDoublet.CayleyArc.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
              (@LieRing.toAddCommGroup.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (@LieRing.ofAssociativeRing.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@CommRing.toRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r)))))
              (@Couret.CayleyDoublet.TripleSupport.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (@LieRing.toAddCommGroup.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@LieRing.ofAssociativeRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (@CommRing.toRing.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                      (ZMod.commRing
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r)))))
                (ZMod.decidableEq
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (@OfNat.ofNat.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (nat_lit 1)
                  (@One.toOfNat1.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (@AddMonoidWithOne.toOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                          (@CommRing.toRing.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))))))))
                (@Nat.cast.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@AddMonoidWithOne.toNatCast.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                      (@Ring.toAddGroupWithOne.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                        (@CommRing.toRing.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                          (ZMod.commRing
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) r)))
                (@Nat.cast.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@AddMonoidWithOne.toNatCast.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                      (@Ring.toAddGroupWithOne.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                        (@CommRing.toRing.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                          (ZMod.commRing
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) r)))
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r)))
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (fun x =>
                  ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r)))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@Equiv.instEquivLike.{1, 1}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))))
                f x)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r)))
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (fun x =>
                  ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r)))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                  (@Equiv.instEquivLike.{1, 1}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) r))))
                f y))) →
        False := @_root_.Couret.CayleyDoublet.p2m_local_cayley_twelve_mul_nonisomorphic

