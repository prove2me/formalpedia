-- Prove2me | solution 1 for mme_recursive_yz_boundary_exact_code_card
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T12:51:36.530909+00:00
-- url     : https://prove2.me/submissions/1d191971-99d6-4ea3-bb8f-2684f6310a0f

import Definitions.Def_mme_recursive_yz_boundary_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem count_lifts {X S : Type*} [Fintype X] [Fintype S] [DecidableEq S]
    (label : X → S) (L : ℕ) (mu : S → ℕ) (hsum : ∑ s, mu s = L) :
    Fintype.card {x : Fin L → X // ∀ s,
      Fintype.card {p : Fin L // label (x p) = s} = mu s} =
      (L.factorial / ∏ s, (mu s).factorial) *
        ∏ s, (Fintype.card {a : X // label a = s}) ^ mu s := by
  classical
  let F := {f : Fin L → S // ∀ s, Fintype.card {p // f p = s} = mu s}
  let E : {x : Fin L → X // ∀ s,
      Fintype.card {p : Fin L // label (x p) = s} = mu s} ≃
      (Σ f : F, ∀ p, {a : X // label a = f.val p}) := {
    toFun := fun x ↦ ⟨⟨fun p ↦ label (x.val p), x.property⟩, fun p ↦ ⟨x.val p, rfl⟩⟩
    invFun := fun y ↦ ⟨fun p ↦ (y.2 p).val, by
      intro s
      have h : (fun p ↦ label (y.2 p).val) = y.1.val :=
        funext (fun p ↦ (y.2 p).property)
      exact (Fintype.card_congr (Equiv.subtypeEquivRight
        (fun p ↦ by rw [(y.2 p).property]))).trans (y.1.property s)⟩
    left_inv := by intro x; rfl
    right_inv := by
      intro y
      rcases y with ⟨⟨f,hf⟩,x⟩
      have h : (fun p ↦ label (x p).val) = f := funext (fun p ↦ (x p).property)
      apply Sigma.ext (Subtype.ext h)
      apply Function.hfunext rfl
      intro p p' hp
      cases hp
      exact (Subtype.heq_iff_coe_eq (fun a ↦ by
        change label a = label (x p).val ↔ label a = f p
        rw [(x p).property])).mpr rfl }
  rw [Fintype.card_congr E, Fintype.card_sigma]
  have hp (f : F) : (∏ p, Fintype.card {a : X // label a = f.val p}) =
      ∏ s, (Fintype.card {a : X // label a = s}) ^ mu s := by
    calc
      _ = ∏ s, ∏ _p : {p // f.val p = s}, Fintype.card {a : X // label a = s} :=
        (Fintype.prod_fiberwise' f.val (fun s ↦ Fintype.card {a : X // label a = s})).symm
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, f.property]
  simp_rw [Fintype.card_pi, hp]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simpa [F] using mme_fintype_prescribed_fiber_function_card (α := Fin L) mu (by simpa using hsum)

private theorem label_fiber_card (ell : ℕ) (s : CompleteWord ell) :
    Fintype.card {x : Letters ell // labels x = s} = 5 ^ ones s := by
  classical
  let E : {x : Letters ell // labels x = s} ≃
      (∀ r, {a : Fin 7 // MME.cwSquareCoordGrade 5 a = s r}) := {
    toFun := fun x r ↦ ⟨x.val r, congrFun x.property r⟩
    invFun := fun x ↦ ⟨fun r ↦ (x r).val, funext (fun r ↦ (x r).property)⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  rw [Fintype.card_congr E, Fintype.card_pi]
  have hc (a : Fin 3) : Fintype.card {x : Fin 7 // MME.cwSquareCoordGrade 5 x = a} =
      if a = 1 then 5 else 1 := by fin_cases a <;> decide
  simp_rw [hc]
  rw [Finset.prod_ite]
  simp [ones]

theorem solution {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L) :
    Fintype.card (Code ell L B.count) = B.dim := by
  classical
  rw [show Fintype.card (Code ell L B.count) = _ from
    count_lifts (@labels ell) L B.count B.total]
  simp_rw [label_fiber_card, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [MME.RecursiveYZ.Boundary.Profile.dim, Nat.mul_comm]
