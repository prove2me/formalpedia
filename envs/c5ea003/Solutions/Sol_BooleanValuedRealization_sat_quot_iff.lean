-- Prove2me | solution 1 for BooleanValuedRealization.sat_quot_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:22:00.977857+00:00
-- url     : https://prove2.me/submissions/4679a8cb-05b2-4c63-8ae0-794ce85fa737

import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_ButtonsSwitches

open BooleanValuedRealization

variable {α : Type*} {B : Type*} [BooleanAlgebra B]

theorem Generic.mem_himp_iff (U : Generic B) (a b : B) :
    U.mem (a ⇨ b) ↔ (U.mem a → U.mem b) := by
  constructor
  · intro hab ha
    exact U.up (U.inf_mem ha hab) (inf_himp_le (a := a) (b := b))
  · intro h
    rcases U.decides a with ha | hna
    · -- himp_eq : a ⇨ b = b ⊔ aᶜ, so b ≤ a ⇨ b
      have hle : b ≤ a ⇨ b := by
        rw [himp_eq]; exact le_sup_left
      exact U.up (h ha) hle
    · -- aᶜ ≤ b ⊔ aᶜ = a ⇨ b
      have hle : aᶜ ≤ a ⇨ b := by
        rw [himp_eq]; exact le_sup_right
      exact U.up hna hle

theorem solution (v : α → B) (U : Generic B) (p : BForm α) :
    sat (quot v U) p ↔ U.mem (bval v p) := by
  induction p with
  | atom a => simp [sat, quot, bval]
  | fls =>
      constructor
      · intro hfalse; exact False.elim hfalse
      · intro hmem; exact False.elim (U.bot_notMem hmem)
  | imp p q ihp ihq =>
      change (sat (quot v U) p → sat (quot v U) q) ↔ U.mem (bval v p ⇨ bval v q)
      rw [Generic.mem_himp_iff, ihp, ihq]
