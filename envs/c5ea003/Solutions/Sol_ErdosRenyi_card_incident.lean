-- Prove2me | solution 1 for ErdosRenyi.card_incident
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:06:23.162115+00:00
-- url     : https://prove2.me/submissions/68b47f9f-4a28-461c-b0b6-6ce0be34e078

import Mathlib
import Definitions.Def_Probability_NumberTheory_ErdosRenyiThreshold
open ErdosRenyi in
theorem solution {n : ℕ} (v : Fin n) : (incident v).card = n - 1 := by
  classical
  -- the edges at `v` are the pairs `s(v, w)` with `w ≠ v`
  have h : (Finset.univ.erase v).card = (incident v).card := by
    refine Finset.card_bij (fun w hw => (⟨s(v, w), by
        rw [Sym2.mk_isDiag_iff]; exact (Finset.ne_of_mem_erase hw).symm⟩ : Edge n)) ?_ ?_ ?_
    · intro w hw
      simp [incident]
    · intro w1 hw1 w2 _ heq
      have h := congrArg Subtype.val heq
      rcases Sym2.eq_iff.mp h with ⟨-, h12⟩ | ⟨-, hv1⟩
      · exact h12
      · exact absurd hv1 (Finset.ne_of_mem_erase hw1)
    · intro e he
      simp only [incident, Finset.mem_filter, Finset.mem_univ, true_and] at he
      refine ⟨Sym2.Mem.other he, ?_, ?_⟩
      · rw [Finset.mem_erase]
        refine ⟨fun hvo => e.2 ?_, Finset.mem_univ _⟩
        rw [← Sym2.other_spec he, hvo]
        exact Sym2.mk_isDiag_iff.mpr rfl
      · exact Subtype.ext (Sym2.other_spec he)
  rw [← h, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
