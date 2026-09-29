-- Prove2me | solution 1 for mme_rectangular_MM_support_min_pair_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:08:34.186707+00:00
-- url     : https://prove2.me/submissions/8f77c090-b0d2-4f7c-8008-81ac75d59b9b

import Theorems.Thm_mme_ordered_rectangular_MM_support_half_pair_matching
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

private theorem realize_image
    {I X Y Z : Type} [Fintype I] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (edge : I → X × Y × Z)
    (hxy : Function.Injective (fun i ↦ ((edge i).1, (edge i).2.1)))
    (hyz : Function.Injective (fun i ↦ ((edge i).2.1, (edge i).2.2)))
    (hzx : Function.Injective (fun i ↦ ((edge i).2.2, (edge i).1)))
    (hinduced : ∀ x y z : I,
      (edge x).2.1 = (edge y).2.1 →
      (edge y).2.2 = (edge z).2.2 →
      (edge z).1 = (edge x).1 → x = y ∧ y = z) :
    ∃ E : Finset (X × Y × Z),
      Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E, x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 → x = y ∧ y = z) ∧
      E.card = Fintype.card I := by
  classical
  let E := Finset.univ.image edge
  have preimage : ∀ e : E, ∃ i, edge i = e.1 := by
    intro e
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp e.2
    exact ⟨i, hi⟩
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    obtain ⟨i, hi⟩ := preimage x
    obtain ⟨j, hj⟩ := preimage y
    apply Subtype.ext
    rw [← hi, ← hj]
    exact congrArg edge (hxy (by simpa only [hi, hj] using h))
  · intro x y h
    obtain ⟨i, hi⟩ := preimage x
    obtain ⟨j, hj⟩ := preimage y
    apply Subtype.ext
    rw [← hi, ← hj]
    exact congrArg edge (hyz (by simpa only [hi, hj] using h))
  · intro x y h
    obtain ⟨i, hi⟩ := preimage x
    obtain ⟨j, hj⟩ := preimage y
    apply Subtype.ext
    rw [← hi, ← hj]
    exact congrArg edge (hzx (by simpa only [hi, hj] using h))
  · intro x y z hxy hyz hzx
    obtain ⟨i, hi⟩ := preimage x
    obtain ⟨j, hj⟩ := preimage y
    obtain ⟨k, hk⟩ := preimage z
    obtain ⟨hij, hjk⟩ := hinduced i j k
      (by simpa only [hi, hj] using hxy)
      (by simpa only [hj, hk] using hyz)
      (by simpa only [hk, hi] using hzx)
    constructor
    · exact Subtype.ext (hi.symm.trans ((congrArg edge hij).trans hj))
    · exact Subtype.ext (hj.symm.trans ((congrArg edge hjk).trans hk))
  · rw [Finset.card_image_of_injective _ (by
      intro i j h
      exact hxy (congrArg (fun e : X × Y × Z ↦ (e.1, e.2.1)) h))]
    exact Finset.card_univ

private def Matching (H V W : ℕ) (lower : ℝ) : Prop :=
  ∃ E : Finset (Fin H × Fin V × Fin W),
    Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)) ∧
    Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)) ∧
    Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)) ∧
    (∀ x y z : E, x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 →
      z.1.1 = x.1.1 → x = y ∧ y = z) ∧ lower ≤ (E.card : ℝ)

private noncomputable def matchingLower (H V W : ℕ) : ℝ :=
  (((min (H * V) (min (H * W) (V * W)) : ℕ) : ℝ) / 2) *
    Real.exp (-100 * Real.sqrt
      (Real.log (((min H (min V W) + 1 : ℕ) : ℝ))))

private theorem rotate_matching {H V W : ℕ} {lower : ℝ}
    (h : Matching H V W lower) : Matching V W H lower := by
  classical
  obtain ⟨E, hxy, hyz, hzx, hinduced, hcard⟩ := h
  let edge : E → Fin V × Fin W × Fin H := fun e ↦ (e.1.2.1, e.1.2.2, e.1.1)
  obtain ⟨F, hfxy, hfyz, hfzx, hfinduced, hfcard⟩ :=
    realize_image edge hyz hzx hxy (by
      intro i j k hy hz hx
      obtain ⟨hki, hij⟩ := hinduced k i j hx hy hz
      exact ⟨hij, hij.symm.trans hki.symm⟩)
  refine ⟨F, hfxy, hfyz, hfzx, hfinduced, ?_⟩
  have hcount : F.card = E.card := by simpa using hfcard
  simpa only [hcount] using hcard

private theorem swap_matching {H V W : ℕ} {lower : ℝ}
    (h : Matching H V W lower) : Matching V H W lower := by
  classical
  obtain ⟨E, hxy, hyz, hzx, hinduced, hcard⟩ := h
  let edge : E → Fin V × Fin H × Fin W := fun e ↦ (e.1.2.1, e.1.1, e.1.2.2)
  have hfxy : Function.Injective (fun e ↦ ((edge e).1, (edge e).2.1)) := by
    intro i j hij
    apply hxy
    simpa only [Prod.swap_prod_mk] using congrArg Prod.swap hij
  have hfyz : Function.Injective (fun e ↦ ((edge e).2.1, (edge e).2.2)) := by
    intro i j hij
    apply hzx
    simpa only [Prod.swap_prod_mk] using congrArg Prod.swap hij
  have hfzx : Function.Injective (fun e ↦ ((edge e).2.2, (edge e).1)) := by
    intro i j hij
    apply hyz
    simpa only [Prod.swap_prod_mk] using congrArg Prod.swap hij
  obtain ⟨F, hFxy, hFyz, hFzx, hFinduced, hFcard⟩ :=
    realize_image edge hfxy hfyz hfzx (by
      intro i j k hx hz hy
      obtain ⟨hik, hkj⟩ := hinduced i k j hy.symm hz.symm hx.symm
      exact ⟨hik.trans hkj, hkj.symm⟩)
  refine ⟨F, hFxy, hFyz, hFzx, hFinduced, ?_⟩
  have hcount : F.card = E.card := by simpa using hFcard
  simpa only [hcount] using hcard

private theorem lower_rotate (H V W : ℕ) :
    matchingLower V W H = matchingLower H V W := by
  have hp : min (V * W) (min (V * H) (W * H)) =
      min (H * V) (min (H * W) (V * W)) := by ac_rfl
  have hm : min V (min W H) = min H (min V W) := by ac_rfl
  simp only [matchingLower, hp, hm]

private theorem lower_swap (H V W : ℕ) :
    matchingLower V H W = matchingLower H V W := by
  have hp : min (V * H) (min (V * W) (H * W)) =
      min (H * V) (min (H * W) (V * W)) := by ac_rfl
  have hm : min V (min H W) = min H (min V W) := by ac_rfl
  simp only [matchingLower, hp, hm]

private theorem rotate {H V W : ℕ}
    (h : Matching H V W (matchingLower H V W)) :
    Matching V W H (matchingLower V W H) := by
  rw [lower_rotate]
  exact rotate_matching h

private theorem swap {H V W : ℕ}
    (h : Matching H V W (matchingLower H V W)) :
    Matching V H W (matchingLower V H W) := by
  rw [lower_swap]
  exact swap_matching h

private theorem ordered (H V W : ℕ) (hH : 0 < H) (hHV : H ≤ V) (hVW : V ≤ W) :
    Matching H V W (matchingLower H V W) := by
  have hp₁ : H * V ≤ H * W := Nat.mul_le_mul_left H hVW
  have hp₂ : H * V ≤ V * W := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right V (hHV.trans hVW)
  have heq : matchingLower H V W =
      ((H : ℝ) * (V : ℝ) / 2) *
        Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) := by
    simp only [matchingLower, min_eq_left (le_min hp₁ hp₂),
      min_eq_left hVW, min_eq_left hHV, Nat.cast_mul]
  rw [heq]
  exact mme_ordered_rectangular_MM_support_half_pair_matching H V W hH hHV hVW

/-- Arbitrary positive rectangular sides, with the true minimum pair capacity
and actual matching transport through all six orderings. -/
theorem solution (H V W : ℕ) (hH : 0 < H) (hV : 0 < V) (hW : 0 < W) :
    ∃ E : Finset (Fin H × Fin V × Fin W),
      Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E, x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 → x = y ∧ y = z) ∧
      (((min (H * V) (min (H * W) (V * W)) : ℕ) : ℝ) / 2) *
          Real.exp (-100 * Real.sqrt
            (Real.log (((min H (min V W) + 1 : ℕ) : ℝ)))) ≤
        (E.card : ℝ) := by
  change Matching H V W (matchingLower H V W)
  rcases le_total H V with hHV | hVH
  · rcases le_total V W with hVW | hWV
    · exact ordered H V W hH hHV hVW
    · rcases le_total H W with hHW | hWH
      · exact rotate (swap (ordered H W V hH hHW hWV))
      · exact rotate (ordered W H V hW hWH hHV)
  · rcases le_total H W with hHW | hWH
    · exact swap (ordered V H W hV hVH hHW)
    · rcases le_total V W with hVW | hWV
      · exact rotate (rotate (ordered V W H hV hVW hWH))
      · exact swap (rotate (ordered W V H hW hWV hVH))

