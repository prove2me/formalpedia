-- Prove2me | solution 1 for TropicalModal.modal_equiv_implies_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:38:18.893755+00:00
-- url     : https://prove2.me/submissions/179415bf-0835-4f51-a1e3-c6667b58331d

import Mathlib
import Definitions.Def_Bridges_TropicalGodelKripkeReconstruction
open Finset BigOperators TropicalModal in
theorem solution {α PropVar : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar)
    (d : ℕ) (x y : α)
    (hmodal : ∀ φ : ModalFormula PropVar, ModalDepth φ ≤ d →
      evalModal F V φ x = evalModal F V φ y) :
    SameTropicalSpectrumUpToDepth F V d x y := by
  intro p k hk
  -- the formula `◇^k p` has depth `k` and evaluates to the `k`-fold tropical diamond of `p`
  have hev : ∀ k : ℕ,
      (∀ z, evalModal F V ((ModalFormula.diamond)^[k] (ModalFormula.atom p)) z
        = iteratedDiamond F k (V.val p) z) ∧
      ModalDepth ((ModalFormula.diamond)^[k] (ModalFormula.atom p)) = k := by
    intro k
    induction k with
    | zero => exact ⟨fun z => rfl, rfl⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨fun z => ?_, ?_⟩
      · show diamondEval F (evalModal F V ((ModalFormula.diamond)^[k] (ModalFormula.atom p))) z
          = diamondEval F (iteratedDiamond F k (V.val p)) z
        congr 1
        funext y
        exact ih.1 y
      · show ModalDepth ((ModalFormula.diamond)^[k] (ModalFormula.atom p)) + 1 = k + 1
        rw [ih.2]
  have h := hmodal ((ModalFormula.diamond)^[k] (ModalFormula.atom p)) (by rw [(hev k).2]; exact hk)
  rw [← (hev k).1 x, ← (hev k).1 y]
  exact h
