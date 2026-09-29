-- Prove2me | solution 1 for mme_regional_prescribed_profile_card
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:34:07.5396+00:00
-- url     : https://prove2.me/submissions/cc1996b6-6034-4df7-92f1-f9dc29c6e69b

import Definitions.Def_mme_recursive_thin_split_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib
open BigOperators MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution {R : Type*} [Fintype R] {A : R → Type*} [∀ r, Fintype (A r)]
    (n : R → ℕ) (mu : ∀ r, A r → ℕ) (hm : ∀ r, ∑ a, mu r a = n r) :
    Fintype.card {w : ∀ r, Fin (n r) → A r // ∀ r a, count (w r) a = mu r a} =
      ∏ r, (n r).factorial / ∏ a, (mu r a).factorial := by
  classical
  let U (r : R) := {w : Fin (n r) → A r // ∀ a, count w a = mu r a}
  let e : {w : ∀ r, Fin (n r) → A r // ∀ r a, count (w r) a = mu r a} ≃ (∀ r, U r) :=
    { toFun := fun w r ↦ ⟨w.val r,w.property r⟩
      invFun := fun w ↦ ⟨fun r ↦ (w r).val,fun r ↦ (w r).property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e,Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro r hr
  have hc := mme_fintype_prescribed_fiber_function_card (α := Fin (n r)) (mu r)
    (by simpa using hm r)
  simpa only [U,count,Fintype.card_subtype,Fintype.card_fin] using hc
