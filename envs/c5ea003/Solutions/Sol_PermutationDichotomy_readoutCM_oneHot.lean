-- Prove2me | solution 1 for PermutationDichotomy.readoutCM_oneHot
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T01:09:23.253618+00:00
-- url     : https://prove2.me/submissions/4c64e6c0-a90f-4fb2-9968-8703b5031789

/-
# `PermutationDichotomy.readoutCM_oneHot`
Target `b19be99e-3825-4fe0-8f6d-a5012f47af95` (recorded Open, not deprecated, at submission time).

## How this is proved
By reduction to the platform node `ContinuousUniversality.readoutCM_oneHot`
(`f849463b-cc93-4851-806e-30f25382d9f5`), which the platform records as Proved.

The two statements read identically, but each namespace declares its own copy of the architecture:
`PermutationDichotomy.readoutCM` and `ContinuousUniversality.readoutCM` are distinct constants with
byte-identical bodies (same `toFun`, same continuity proof). `Seq` is an `abbrev` on both sides
reducing to `ι → κ → ℝ`. The bridge lemma below equates the two readouts; it is stated so that the
cheap definitional route is tried first and an extensional argument is used only if needed.

## Disclosures
The imported node is the only external fact used. It enters through the platform's `Theorems`
mirror and is not reproduced, so `#print axioms solution` reports `sorryAx` from that mirror alone.
The audit module `Solutions/AxFree_dup_b19be99e.lean` binds the imported statement as a hypothesis
and rebuilds the same proof term from it. Binders are copied verbatim from the target's mirror.
-/
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PermutationDichotomy
import Theorems.Thm_ContinuousUniversality_readoutCM_oneHot

set_option autoImplicit false

namespace DupBridge

/-- The two namespaces' readout maps are the same continuous map. -/
theorem readoutCM_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (w : ι → κ → ℝ) :
    PermutationDichotomy.readoutCM w = ContinuousUniversality.readoutCM w := by
  first
  | rfl
  | · ext y
      simp [PermutationDichotomy.readoutCM, ContinuousUniversality.readoutCM]

end DupBridge

open PermutationDichotomy in
/-- **The target, verbatim.** Reduction to the Proved node `f849463b`. -/
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (i₀ : ι) (a₀ : κ) (x : Seq ι κ) :
    readoutCM (fun i a => if i = i₀ ∧ a = a₀ then (1:ℝ) else 0) x = x i₀ a₀ := by
  first
  | exact ContinuousUniversality.readoutCM_oneHot i₀ a₀ x
  | · rw [DupBridge.readoutCM_eq]
      exact ContinuousUniversality.readoutCM_oneHot i₀ a₀ x
