-- Prove2me | solution 1 for Couret.shiftMaskOn_support
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:59.547447+00:00
-- url     : https://prove2.me/submissions/a324b687-3ff1-4136-9690-33846983d19b

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Theorems.Thm_Couret_maskSupport_or
import Theorems.Thm_Couret_maskSupport_singleton
import Theorems.Thm_Couret_maskSupport_zero
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret







































theorem p2m_local_shiftMaskOn_support (g : Code30) (mask : Nat) (letters : List Code30)
    (u : Code30) :
    maskSupport (shiftMaskOn g mask letters) u ↔
      ∃ v, v ∈ letters ∧ maskSupport mask v ∧ mul30 g v = u := by
  induction letters with
  | nil => simp [shiftMaskOn, maskSupport]
  | cons a rest ih =>
    simp only [shiftMaskOn, maskSupport_or]
    by_cases h : maskSupport mask a
    · simp only [if_pos h, maskSupport_singleton, ih]
      constructor
      · intro he
        rcases he with he | ⟨v,hv,hm,hprod⟩
        · exact ⟨a, List.mem_cons_self, h, he.symm⟩
        · exact ⟨v, List.mem_cons_of_mem _ hv, hm, hprod⟩
      · rintro ⟨v,hv,hm,hprod⟩
        rcases List.mem_cons.mp hv with rfl | hv
        · exact Or.inl hprod.symm
        · exact Or.inr ⟨v,hv,hm,hprod⟩
    · simp only [if_neg h, maskSupport_zero, false_or, ih]
      constructor
      · rintro ⟨v,hv,hm,hprod⟩
        exact ⟨v,List.mem_cons_of_mem _ hv,hm,hprod⟩
      · rintro ⟨v,hv,hm,hprod⟩
        rcases List.mem_cons.mp hv with rfl | hv
        · exact False.elim (h hm)
        · exact ⟨v,hv,hm,hprod⟩











































end Couret


theorem solution : ∀ (g : Couret.Code30) (mask : Nat) (letters : List.{0} Couret.Code30) (u : Couret.Code30),
  Iff (Couret.maskSupport (Couret.shiftMaskOn g mask letters) u)
    (@Exists.{1} Couret.Code30 fun v =>
      And
        (@Membership.mem.{0, 0} Couret.Code30 (List.{0} Couret.Code30) (@List.instMembership.{0} Couret.Code30) letters
          v)
        (And (Couret.maskSupport mask v) (@Eq.{1} Couret.Code30 (Couret.mul30 g v) u))) := @_root_.Couret.p2m_local_shiftMaskOn_support

