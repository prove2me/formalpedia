-- Prove2me | solution 1 for mme_CW_q6_common_halving_fiber_half_pattern_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:17:43.231676+00:00
-- url     : https://prove2.me/submissions/896aa01c-6f31-491a-899e-54e00d5225c6

import Definitions.Def_mme_CW_q6_common_paired_halving
import Mathlib.Data.Fintype.Card

open MME
set_option autoImplicit false

private theorem supported_x_unique (x y z x' y' z' : Fin 3)
    (h : (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1) ∨
      (x = 0 ∧ y = 1 ∧ z = 2) ∨ (x = 1 ∧ y = 0 ∧ z = 2))
    (h' : (x' = 0 ∧ y' = 0 ∧ z' = 0) ∨ (x' = 1 ∧ y' = 1 ∧ z' = 1) ∨
      (x' = 0 ∧ y' = 1 ∧ z' = 2) ∨ (x' = 1 ∧ y' = 0 ∧ z' = 2))
    (hy : y = y') (hz : z = z') : x = x' := by
  rcases h with h | h | h | h <;>
    rcases h' with h' | h' | h' | h' <;> omega

/-- Within one color, the shared third-coordinate word lets the first X
half and the second Y half jointly identify an entry. Thus their distinct
pattern counts have product at least the fiber size. -/
theorem solution
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A) :
    let PX := Finset.univ.image (fun h : Fin H ↦
      fun r : Fin N ↦ (family.entry (a,h)).val 0 (halving.position (Sum.inl r)))
    let PY := Finset.univ.image (fun h : Fin H ↦
      fun r : Fin N ↦ (family.entry (a,h)).val 1 (halving.position (Sum.inr r)))
    H ≤ PX.card * PY.card := by
  intro PX PY
  classical
  let x := fun h : Fin H ↦
    fun r : Fin N ↦ (family.entry (a,h)).val 0 (halving.position (Sum.inl r))
  let y := fun h : Fin H ↦
    fun r : Fin N ↦ (family.entry (a,h)).val 1 (halving.position (Sum.inr r))
  have hi : Function.Injective (fun h ↦ (x h, y h)) := by
    intro h k he
    have hx : (family.entry (a,h)).val 0 = (family.entry (a,k)).val 0 := by
      funext j
      obtain ⟨r, rfl⟩ := halving.position.surjective j
      cases r with
      | inl r => exact congrFun (congrArg Prod.fst he) r
      | inr r =>
        exact supported_x_unique _ _ _ _ _ _
          ((family.entry (a,h)).property.1 (halving.position (Sum.inr r)))
          ((family.entry (a,k)).property.1 (halving.position (Sum.inr r)))
          (congrFun (congrArg Prod.snd he) r)
          (congrFun (family.zSameFiber a h k) (halving.position (Sum.inr r)))
    exact congrArg Prod.snd (family.xInjective hx)
  let f : Fin H → {b // b ∈ PX} × {b // b ∈ PY} := fun h ↦
    (⟨x h, Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩⟩,
     ⟨y h, Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩⟩)
  have hf : Function.Injective f := by
    intro h k he
    apply hi
    exact congrArg (fun v : {b // b ∈ PX} × {b // b ∈ PY} ↦ (v.1.val, v.2.val)) he
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

#print axioms solution
