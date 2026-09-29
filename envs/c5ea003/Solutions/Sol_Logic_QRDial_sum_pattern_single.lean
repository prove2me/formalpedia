-- Prove2me | solution 1 for Logic.QRDial.sum_pattern_single
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:12:50.140562+00:00
-- url     : https://prove2.me/submissions/29cb4f7e-1571-4aed-8e13-cc75c0512202

import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Definitions.Def_Logic_QRDialOrthogonality
open Logic.QRDial in
theorem solution {σ : Type*} [Fintype σ] (a : σ → ℝ) (ha : ∑ s, a s = 0) :
    ∀ k : ℕ, ∑ w : Fin k → σ, (∑ i, a (w i)) = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => σ)) (fun w => ∑ i, a (w i)),
      Fintype.sum_prod_type]
    have hterm : ∀ (s : σ) (v : Fin k → σ),
        (∑ i : Fin (k + 1), a ((Fin.consEquiv (fun _ : Fin (k + 1) => σ)) (s, v) i))
          = a s + ∑ i : Fin k, a (v i) := by
      intro s v
      rw [Fin.sum_univ_succ]
      simp [Fin.consEquiv]
    simp only [hterm]
    have hrow : ∀ s : σ, (∑ _v : Fin k → σ, (a s + ∑ i : Fin k, a (_v i)))
        = (Fintype.card (Fin k → σ)) • a s := by
      intro s
      rw [Finset.sum_add_distrib, ih, add_zero, Finset.sum_const, Finset.card_univ]
    simp only [hrow]
    rw [← Finset.smul_sum, ha, smul_zero]
