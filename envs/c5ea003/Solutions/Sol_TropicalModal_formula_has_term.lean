-- Prove2me | solution 1 for TropicalModal.formula_has_term
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:32:42.102787+00:00
-- url     : https://prove2.me/submissions/4c72b50f-1ad9-43a5-aa05-8db03316b12e

import Mathlib
import Definitions.Def_Bridges_TropicalGodelKripkeReconstruction
open Finset BigOperators TropicalModal in
theorem solution {α PropVar : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar) :
    ∀ φ : ModalFormula PropVar,
      ∃ t : TropicalTerm PropVar,
        t.maxDepth ≤ ModalDepth φ ∧
        ∀ z : α, evalModal F V φ z = evalTerm F V t z := by
  -- the tropical diamond distributes over pointwise minima
  have hdist : ∀ (v w : α → ℝ) (z : α), diamondEval F (fun y => min (v y) (w y)) z
      = min (diamondEval F v z) (diamondEval F w z) := by
    intro v w z
    unfold diamondEval
    apply le_antisymm
    · refine le_min (Finset.le_inf' _ _ (fun y _ => ?_)) (Finset.le_inf' _ _ (fun y _ => ?_))
      · refine (Finset.inf'_le _ (mem_univ y)).trans ?_
        show F.A z y + min (v y) (w y) ≤ F.A z y + v y
        linarith [min_le_left (v y) (w y)]
      · refine (Finset.inf'_le _ (mem_univ y)).trans ?_
        show F.A z y + min (v y) (w y) ≤ F.A z y + w y
        linarith [min_le_right (v y) (w y)]
    · refine Finset.le_inf' _ _ (fun y _ => ?_)
      show min _ _ ≤ F.A z y + min (v y) (w y)
      rcases min_choice (v y) (w y) with h | h
      · rw [h]
        exact (min_le_left _ _).trans (Finset.inf'_le (fun y => F.A z y + v y) (mem_univ y))
      · rw [h]
        exact (min_le_right _ _).trans (Finset.inf'_le (fun y => F.A z y + w y) (mem_univ y))
  -- shifting a term applies one diamond and raises its depth by one
  have hshift : ∀ t : TropicalTerm PropVar,
      (∀ z, evalTerm F V t.shift z = diamondEval F (evalTerm F V t) z) ∧
        t.shift.maxDepth = t.maxDepth + 1 := by
    intro t
    induction t with
    | single k p => exact ⟨fun z => rfl, rfl⟩
    | minOf t1 t2 ih1 ih2 =>
      refine ⟨fun z => ?_, ?_⟩
      · show min (evalTerm F V t1.shift z) (evalTerm F V t2.shift z)
          = diamondEval F (fun y => min (evalTerm F V t1 y) (evalTerm F V t2 y)) z
        rw [ih1.1, ih2.1, hdist]
      · show max t1.shift.maxDepth t2.shift.maxDepth = max t1.maxDepth t2.maxDepth + 1
        rw [ih1.2, ih2.2]
        omega
  intro φ
  induction φ with
  | atom p => exact ⟨.single 0 p, le_of_eq rfl, fun z => rfl⟩
  | conj φ ψ ihφ ihψ =>
    obtain ⟨t1, h1, e1⟩ := ihφ
    obtain ⟨t2, h2, e2⟩ := ihψ
    refine ⟨.minOf t1 t2, ?_, fun z => ?_⟩
    · show max t1.maxDepth t2.maxDepth ≤ max (ModalDepth φ) (ModalDepth ψ)
      omega
    · show min (evalModal F V φ z) (evalModal F V ψ z) = min (evalTerm F V t1 z) (evalTerm F V t2 z)
      rw [e1, e2]
  | diamond φ ih =>
    obtain ⟨t, h, e⟩ := ih
    refine ⟨t.shift, ?_, fun z => ?_⟩
    · rw [(hshift t).2]
      show t.maxDepth + 1 ≤ ModalDepth φ + 1
      omega
    · rw [(hshift t).1]
      show diamondEval F (evalModal F V φ) z = diamondEval F (evalTerm F V t) z
      congr 1
      funext y
      exact e y
