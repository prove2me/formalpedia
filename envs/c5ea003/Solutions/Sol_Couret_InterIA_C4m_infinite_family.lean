-- Prove2me | solution 1 for Couret.InterIA.C4m.infinite_family
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:41.613861+00:00
-- url     : https://prove2.me/submissions/ba82c65d-f200-4d74-8ecb-f4ae982544b3

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
import Theorems.Thm_Couret_InterIA_C4m_encoded_squares_equal
import Theorems.Thm_Couret_InterIA_C4m_entries_distinct
import Theorems.Thm_Couret_InterIA_C4m_no_two_torsion_translate
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
















variable {G : Type*} [AddCommGroup G] [DecidableEq G]



theorem encode_square_coeff (S : Finset G) (z : G) :
    (encode S * encode S) z = (orderedSquare S z : ℤ) := by
  have eval_sum (s : Finset G) (f : G → AddMonoidAlgebra ℤ G) :
      (∑ a ∈ s, f a) z = ∑ a ∈ s, (f a) z := by
    exact map_sum ((Finsupp.applyAddHom z).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom) f s
  simp only [encode, Finset.sum_mul, Finset.mul_sum, eval_sum,
    AddMonoidAlgebra.single_mul_single, one_mul, Finsupp.single_apply,
    orderedSquare, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [eq_comm, add_comm]



theorem supports_card (m : ℕ) (hm : 2 ≤ m) : (T m).card = 4 ∧ (U m).card = 4 := by
  obtain ⟨h01,h0m,h0t,h1m,h1t,hmt,h0v,h0u,hmv,hmu,hvu⟩ := entries_distinct m hm
  exact ⟨Finset.card_eq_four.mpr ⟨0,1,_,_,h01,h0m,h0t,h1m,h1t,hmt,rfl⟩,
    Finset.card_eq_four.mpr ⟨0,_,_,_,h0m,h0v,h0u,hmv,hmu,hvu,rfl⟩⟩



/-- The equality is labelled at every residue and counts all ordered pairs. -/
theorem ordered_squares_equal (m : ℕ) (hm : 2 ≤ m) (z : ZMod (4*m)) :
    orderedSquare (T m) z = orderedSquare (U m) z := by
  have h := congrArg (fun a : AddMonoidAlgebra ℤ (ZMod (4*m)) => a z)
    (encoded_squares_equal m hm)
  simpa only [pow_two, encode_square_coeff, Nat.cast_inj] using h









/-- Parametric collision theorem; no bounded enumeration or finite-case oracle. -/
theorem p2m_local_infinite_family (m : ℕ) (hm : 2 ≤ m) :
    (T m).card = 4 ∧ (U m).card = 4 ∧
    (∀ z, orderedSquare (T m) z = orderedSquare (U m) z) ∧
    (∀ u, u+u=0 → translateSupport (T m) u ≠ U m) := by
  exact ⟨(supports_card m hm).1, (supports_card m hm).2,
    ordered_squares_equal m hm, no_two_torsion_translate m hm⟩


end Couret.InterIA.C4m

theorem solution : ∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    And
      (@Eq.{1} Nat
        (@Finset.card.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
          (Couret.InterIA.C4m.T m))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (And
        (@Eq.{1} Nat
          (@Finset.card.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
            (Couret.InterIA.C4m.U m))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (And
          (∀
            (z :
              ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m)),
            @Eq.{1} Nat
              (@Couret.STROBO2TORS.orderedSquare.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                (@Ring.toAddCommGroup.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (@CommRing.toRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))))
                (ZMod.decidableEq
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                (Couret.InterIA.C4m.T m) z)
              (@Couret.STROBO2TORS.orderedSquare.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                (@Ring.toAddCommGroup.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (@CommRing.toRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))))
                (ZMod.decidableEq
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                (Couret.InterIA.C4m.U m) z))
          (∀
            (u :
              ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m)),
            @Eq.{1}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                (@HAdd.hAdd.{0, 0, 0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (@instHAdd.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                    (@Distrib.toAdd.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                      (@instDistribOfSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                        (@CommSemiring.toSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                          (@CommRing.toCommSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m)))))))
                  u u)
                (@OfNat.ofNat.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (nat_lit 0)
                  (@Zero.toOfNat0.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                    (@MulZeroClass.toZero.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                      (@instMulZeroClassOfSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                        (@CommSemiring.toSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                          (@CommRing.toCommSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m)))))))) →
              @Ne.{1}
                (Finset.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m)))
                (@Couret.STROBO2TORS.translateSupport.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (@Ring.toAddCommGroup.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                    (@CommRing.toRing.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                      (ZMod.commRing
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))))
                  (ZMod.decidableEq
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
                  (Couret.InterIA.C4m.T m) u)
                (Couret.InterIA.C4m.U m)))) := @_root_.Couret.InterIA.C4m.p2m_local_infinite_family

