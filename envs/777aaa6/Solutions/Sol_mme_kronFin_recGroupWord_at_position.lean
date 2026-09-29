-- Prove2me | solution 1 for mme_kronFin_recGroupWord_at_position
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:43:00.412277+00:00
-- url     : https://prove2.me/submissions/3e878b3d-55cc-4955-a311-2647be141749

import Definitions.Def_mme_kronFin_rec_group_position_equiv_data

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem appendLeft
    {m n : ℕ} {indexA : Fin m → Type u}
    {indexB : Fin n → Type u}
    (w : ∀ r, TensorObj.recAppendFamily m n indexA indexB r) (a : Fin m) :
    HEq (TensorObj.recAppendLeftWord w a)
      (w (TensorObj.recAppendPositionFrom m n (Sum.inl a))) := by
  induction m generalizing n with
  | zero => exact a.elim0
  | succ m ih =>
      refine Fin.cases ?_ (fun q ↦ ?_) a
      · rfl
      · exact ih (w := fun r ↦ w r.succ) q

private theorem appendRight
    {m n : ℕ} {indexA : Fin m → Type u}
    {indexB : Fin n → Type u}
    (w : ∀ r, TensorObj.recAppendFamily m n indexA indexB r) (b : Fin n) :
    HEq (TensorObj.recAppendRightWord w b)
      (w (TensorObj.recAppendPositionFrom m n (Sum.inr b))) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih => exact ih (w := fun r ↦ w r.succ) b

theorem solution
    {k : ℕ} {count : Fin k → ℕ} {index : Fin k → Type u}
    (w : ∀ r, TensorObj.recGroupFamily k count index r)
    (p : Σ s, Fin (count s)) :
    HEq (TensorObj.recGroupWord w p.1 p.2)
      (w ((TensorObj.recGroupPositionEquiv k count).symm p)) := by
  induction k with
  | zero => exact p.1.elim0
  | succ k ih =>
      rcases p with ⟨s, a⟩
      cases s using Fin.cases with
      | zero =>
          change HEq (TensorObj.recAppendLeftWord w a) _
          exact appendLeft w a
      | succ s =>
          have htail := ih (w := TensorObj.recAppendRightWord w) ⟨s, a⟩
          have hright := appendRight w
            ((TensorObj.recGroupPositionEquiv k
              (fun q ↦ count q.succ)).symm ⟨s, a⟩)
          exact htail.trans hright
