-- Prove2me | solution 1 for NeuroSymbolicRLHF.oscil_add_const
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:15:44.006552+00:00
-- url     : https://prove2.me/submissions/de221253-397a-4e1e-ab33-5d46d6b8697a

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry

open Finset Real BigOperators
open NeuroSymbolicRLHF

set_option autoImplicit false

/- Ported from paulklemstine/Lean, commit 53c2925a02,
   Catalog/Speculative/AutoResearch/RLHFHilbertIsometry.lean. -/
private theorem ported_le_sup_univ {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (i : ι) : f i ≤ univ.sup' univ_nonempty f :=
  Finset.le_sup' f (mem_univ i)

private theorem ported_inf_univ_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (i : ι) : univ.inf' univ_nonempty f ≤ f i :=
  Finset.inf'_le f (mem_univ i)

theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (c : ℝ) : oscil (fun i => f i + c) = oscil f := by
  have hs : univ.sup' univ_nonempty (fun i => f i + c) = univ.sup' univ_nonempty f + c := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ ?_
      intro i _
      have := ported_le_sup_univ f i
      linarith
    · have : univ.sup' univ_nonempty f ≤ univ.sup' univ_nonempty (fun i => f i + c) - c := by
        refine Finset.sup'_le _ _ ?_
        intro i _
        have := ported_le_sup_univ (fun i => f i + c) i
        simp only at this
        linarith
      linarith
  have hi : univ.inf' univ_nonempty (fun i => f i + c) = univ.inf' univ_nonempty f + c := by
    apply le_antisymm
    · have : univ.inf' univ_nonempty (fun i => f i + c) - c ≤ univ.inf' univ_nonempty f := by
        refine Finset.le_inf' _ _ ?_
        intro i _
        have := ported_inf_univ_le (fun i => f i + c) i
        simp only at this
        linarith
      linarith
    · refine Finset.le_inf' _ _ ?_
      intro i _
      have := ported_inf_univ_le f i
      linarith
  simp only [oscil, hs, hi]
  ring
