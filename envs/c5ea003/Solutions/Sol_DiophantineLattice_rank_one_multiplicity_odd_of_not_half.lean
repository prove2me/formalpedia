-- Prove2me | solution 1 for DiophantineLattice.rank_one_multiplicity_odd_of_not_half
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:55:54.478742+00:00
-- url     : https://prove2.me/submissions/9e70cf43-ae8c-48fb-8700-1f21f1820766

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeExactOrder
open DiophantineLattice Finset in
theorem solution {t : Fin 1 → ℚ}
    (h2 : ∀ k : Fin 1 → ℤ, (fun i => (2 : ℚ) * t i) ≠ emb k) :
    ∃ (c : ℚ) (S : Finset (Fin 1 → ℤ)),
      (∀ m : Fin 1 → ℤ, m ∈ S ↔ form (1 : Matrix (Fin 1) (Fin 1) ℚ)
        (fun i => t i - emb m i) = c) ∧ ¬ Even S.card := by
  have hone : ∀ x : Fin 1 → ℚ, form (1 : Matrix (Fin 1) (Fin 1) ℚ) x = x 0 ^ 2 := by
    intro x
    simp [form, bil, Matrix.one_apply, Fin.sum_univ_one]
    ring
  refine ⟨t 0 ^ 2, {0}, ?_, ?_⟩
  · intro m
    rw [Finset.mem_singleton, hone]
    simp only [emb]
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      have hm : (m 0 : ℚ) * ((m 0 : ℚ) - 2 * t 0) = 0 := by nlinarith [h]
      rcases mul_eq_zero.mp hm with h0 | h0
      · funext i
        have : i = 0 := Subsingleton.elim i 0
        subst this
        exact_mod_cast h0
      · exfalso
        refine h2 m ?_
        funext i
        have : i = 0 := Subsingleton.elim i 0
        subst this
        simp only [emb]
        linarith [h0]
  · simp
