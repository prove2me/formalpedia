-- Prove2me | Definitions.Def_Novelty_IntegratedInformation
-- name    : Novelty_IntegratedInformation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:42.566333+00:00
-- url     : https://prove2.me/theorems/c6f4cbb8-8744-4a8f-ac83-363b15ac3005
-- title:
--   Aether Catalog definitions — Novelty_IntegratedInformation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.IntegratedInformation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/IntegratedInformation.lean by skeleton subtraction
import Mathlib

/-! # Consciousness as Integrated Information

This file develops a finite mathematical model of integrated information.  A
causal structure has finitely many admissible cuts and a nonnegative loss at
each cut.  Its integrated information `Φ` is the least such loss.  Parallel
composition adds losses, while exclusion selects a maximally integrated member
of a finite family.  Pointwise comparison of loss functions supplies a small
category-like refinement calculus.
-/

open Finset

namespace IntegratedInformation

/-- A finite causal structure consists of admissible interventions (`Cut`) and
the nonnegative causal information destroyed by each intervention. -/
structure CausalStructure where
  Cut : Type
  [finiteCut : Fintype Cut]
  [cutNonempty : Nonempty Cut]
  loss : Cut → ℝ
  loss_nonneg : ∀ c, 0 ≤ loss c

attribute [instance] CausalStructure.finiteCut CausalStructure.cutNonempty

/-- Integrated information `Φ` is the minimum information loss among all
admissible causal cuts. -/
noncomputable def Phi (S : CausalStructure) : ℝ :=
  (Finset.univ.image S.loss).min' (Finset.univ_nonempty.image S.loss)






/-- Parallel composition: a cut chooses one cut in each component and the two
independent information losses add. -/
def tensor (S T : CausalStructure) : CausalStructure where
  Cut := S.Cut × T.Cut
  loss c := S.loss c.1 + T.loss c.2
  loss_nonneg c := add_nonneg (S.loss_nonneg c.1) (T.loss_nonneg c.2)


/-- Pointwise causal refinement: `S ⟶ T` means every cut of `T`, translated to
a cut of `S`, destroys at most as much information in `S`. -/
structure Refinement (S T : CausalStructure) where
  onCut : T.Cut → S.Cut
  loss_le : ∀ c, S.loss (onCut c) ≤ T.loss c





/-- A finite family of candidate complexes on one cut space. -/
structure CandidateFamily (ι : Type) [Fintype ι] [Nonempty ι] where
  system : ι → CausalStructure

/-- The exclusion value is the maximum `Φ` among a finite nonempty family of
candidate complexes. -/
noncomputable def BigPhi {ι : Type} [Fintype ι] [Nonempty ι]
    (F : CandidateFamily ι) : ℝ :=
  (Finset.univ.image (fun i => Phi (F.system i))).max'
    (Finset.univ_nonempty.image fun i => Phi (F.system i))






end IntegratedInformation


