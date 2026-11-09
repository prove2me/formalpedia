-- Prove2me | solution 1 for Couret.decodeMaskState_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:59:54.954341+00:00
-- url     : https://prove2.me/submissions/0a2ef346-eda2-4371-9dc8-b14cd5a0714e

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Theorems.Thm_Couret_canonical_mask_injective
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret



























































theorem p2m_local_decodeMaskState_injective (s t : MaskState) (hs : s.canonical)
    (ht : t.canonical) (he : decodeMaskState s = decodeMaskState t) : s = t := by
  cases s with
  | initial =>
    cases t with
    | initial => rfl
    | active r mask => cases he
  | active r mask =>
    cases t with
    | initial => cases he
    | active r' mask' =>
      have hr : r = r' := (State.active.inj he).1
      have hu : maskSupport mask = maskSupport mask' := (State.active.inj he).2
      have hm : mask = mask' := canonical_mask_injective mask mask' hs ht
        (fun u => Iff.of_eq (congrFun hu u))
      cases hr
      cases hm
      rfl























end Couret


theorem solution : ∀ (s t : Couret.MaskState),
  Couret.MaskState.canonical s →
    Couret.MaskState.canonical t →
      @Eq.{1} (Couret.State.{0} Couret.Code30) (Couret.decodeMaskState s) (Couret.decodeMaskState t) →
        @Eq.{1} Couret.MaskState s t := @_root_.Couret.p2m_local_decodeMaskState_injective

