-- Prove2me | solution 1 for AlmostLossless.blockScheme_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T08:13:32.406701+00:00
-- url     : https://prove2.me/submissions/eacfc569-f611-4c69-93fb-e832b920db47

import Mathlib
import Definitions.Def_Bridges_AlmostLosslessBlockDecoding
import Theorems.Thm_AlmostLossless_blockDec_eq_some_iff
import Theorems.Thm_AlmostLossless_powDist_union_bound
set_option autoImplicit false
open Finset BigOperators NonArchInfoTheory AlmostLossless

variable {β : Type*} [Fintype β] [DecidableEq β] {b m : ℕ}

private theorem succeeds_iff {l : Fin b → List β} {h : Fin b → β → Fin m}
    {x : Fin b → β} :
    (blockScheme l h).Succeeds x ↔ ∀ j, (hashScheme (l j) (h j)).Succeeds (x j) := by
  unfold Scheme.Succeeds blockScheme hashScheme blockEnc
  simpa using (blockDec_eq_some_iff (l := l) (h := h) (c := fun j => h j (x j)) (x := x))

theorem solution (μ : FinProbDist β) (l : Fin b → List β)
    (h : Fin b → β → Fin m) (e : ℝ)
    (hblock : ∀ j, setMass μ (Finset.univ.filter
        (fun y => ¬ (hashScheme (l j) (h j)).Succeeds y)) ≤ e) :
    setMass (powDist μ b) (Finset.univ.filter
        (fun x : Fin b → β => ¬ (blockScheme l h).Succeeds x)) ≤ b * e := by
  classical
  set Bs : Fin b → Finset β := fun j =>
    Finset.univ.filter (fun y => ¬ (hashScheme (l j) (h j)).Succeeds y) with hBs
  have hset : Finset.univ.filter (fun x : Fin b → β => ¬ (blockScheme l h).Succeeds x)
      = Finset.univ.filter (fun x : Fin b → β => ∃ j, x j ∈ Bs j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hBs]
    rw [succeeds_iff]
    push_neg
    constructor
    · rintro ⟨j, hj⟩; exact ⟨j, by simp [hj]⟩
    · rintro ⟨j, hj⟩; exact ⟨j, by simpa using hj⟩
  rw [hset]
  refine le_trans (powDist_union_bound μ b Bs) ?_
  calc ∑ j, setMass μ (Bs j) ≤ ∑ _j : Fin b, e := Finset.sum_le_sum fun j _ => hblock j
    _ = b * e := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

#print axioms solution
