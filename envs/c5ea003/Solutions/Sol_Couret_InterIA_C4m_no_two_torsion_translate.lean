-- Prove2me | solution 1 for Couret.InterIA.C4m.no_two_torsion_translate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:33.800477+00:00
-- url     : https://prove2.me/submissions/bf79c88c-260b-4444-85fb-3f9b9addeef0

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
import Theorems.Thm_Couret_InterIA_C4m_two_torsion_iff
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












theorem cast_eq_iff {m a b : ℕ} (ha : a < 4*m) (hb : b < 4*m) :
    (a : ZMod (4*m)) = (b : ZMod (4*m)) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]



variable {G : Type*} [AddCommGroup G] [DecidableEq G]















theorem one_not_mem_U (m : ℕ) (hm : 2 ≤ m) : (1 : ZMod (4*m)) ∉ U m := by
  have h (a : ℕ) (ha : a < 4*m) (hne : 1 ≠ a) :
      (1 : ZMod (4*m)) ≠ a :=
    by simpa only [Nat.cast_one] using (cast_eq_iff (a:=1) (by omega) ha).not.mpr hne
  have h0 := h 0 (by omega) (by omega)
  have h1 := h m (by omega) (by omega)
  have h2 := h (m+1) (by omega) (by omega)
  have h3 := h (3*m+1) (by omega) (by omega)
  have h0' : (1 : ZMod (4*m)) ≠ 0 := by simpa only [Nat.cast_zero] using h0
  simp only [U, Finset.mem_insert, Finset.mem_singleton, h0',h1,h2,h3,
    or_self, not_false_eq_true]

/-- A fixed witness excludes every two-torsion translate. -/
theorem p2m_local_no_two_torsion_translate (m : ℕ) (hm : 2 ≤ m)
    (u : ZMod (4*m)) (hu : u+u=0) : translateSupport (T m) u ≠ U m := by
  have hin : (1 : ZMod (4*m)) ∈ translateSupport (T m) u := by
    rcases (two_torsion_iff m hm u).mp hu with rfl | rfl
    · simp [translateSupport,T]
    · apply Finset.mem_image.mpr
      refine ⟨((2*m+1 : ℕ) : ZMod (4*m)), by simp [T], ?_⟩
      push_cast
      have hz : (4 : ZMod (4*m)) * m = 0 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using (ZMod.natCast_self (4*m))
      linear_combination hz
  intro heq
  rw [heq] at hin
  exact one_not_mem_U m hm hin






end Couret.InterIA.C4m

theorem solution : ∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    ∀
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
          (Couret.InterIA.C4m.U m) := @_root_.Couret.InterIA.C4m.p2m_local_no_two_torsion_translate

