-- Prove2me | solution 1 for TropicalLA.charCoeff_card_eq_tdet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T09:45:47.684619+00:00
-- url     : https://prove2.me/submissions/e3de1df7-dd72-4aba-b7d1-040eede86b91

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCharPoly
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    charCoeff A (Fintype.card ι) = tdet A := by
  have hmem : ∀ σ : Equiv.Perm ι, ((univ : Finset ι), σ) ∈ admPairs ι (Fintype.card ι) := by
    intro σ
    simp [admPairs]
  have hne : (admPairs ι (Fintype.card ι)).Nonempty := ⟨_, hmem 1⟩
  unfold charCoeff tdet
  rw [dif_pos hne]
  apply le_antisymm
  · apply Finset.sup'_le
    rintro ⟨s, σ⟩ hp
    have hs : s = univ := by
      simp only [admPairs, Finset.mem_filter] at hp
      exact Finset.eq_univ_of_card s hp.2.1
    subst hs
    exact Finset.le_sup' (permWeight A) (mem_univ σ)
  · apply Finset.sup'_le
    intro σ _
    exact Finset.le_sup' (fun p : Finset ι × Equiv.Perm ι => minorWeight A p.1 p.2) (hmem σ)
