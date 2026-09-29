-- Prove2me | Theorems.Thm_HyperAwareness11D_exists_unique_deepSets_params
-- name    : HyperAwareness11D.exists_unique_deepSets_params
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:38:11.849263+00:00
-- url     : https://prove2.me/theorems/21c73f9b-91be-4a6b-a6ff-b2ffb164ee73
-- title:
--   The two Deep Sets parameters are uniquely determined by the layer.
-- statement:
--   The two Deep Sets parameters are uniquely determined by the layer.
--
--   ```lean
--   theorem HyperAwareness11D.exists_unique_deepSets_params(hn : 2 ≤ n) (M : Fin n → Fin n → ℝ)
--       (h : PermEquivariant M) :
--       ∃! p : ℝ × ℝ, ∀ i j, M i j = if i = j then p.1 else p.2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HyperAwareness11D/Equivariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HyperAwareness11D/Equivariance.lean#L163

-- Thm stub generated from MachineLearning/HyperAwareness11D/Equivariance.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Equivariance
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity

/-!
# Hyper-Awareness III: symmetry rigidity of 11-dimensional perception layers

A recurring design proposal for "hyper-aware" architectures is to make the 11 spatial axes
*interchangeable*, i.e. to impose the symmetries of the 11-dimensional hypercube on every
linear layer.  This file proves that such a demand is self-defeating, by computing exactly
which linear layers `x ↦ M x` on `ℝ¹¹` are equivariant for the two natural symmetry groups:

* the symmetric group `S₁₁` (permuting the 11 axes), and
* the hyperoctahedral group `B₁₁ = (ℤ/2)¹¹ ⋊ S₁₁` (permuting *and* reflecting the axes).

## Main results

* `HyperAwareness11D.permEquivariant_iff_entries` — permutation equivariance is exactly the
  statement that `M` has constant diagonal and constant off-diagonal entries.
* `HyperAwareness11D.permEquivariant_deepSets` — hence such a layer has the "Deep Sets" form
  `x ↦ a • x + b • (∑ x)`: **exactly two learnable parameters**, versus `121` for a general
  `11 × 11` layer.
* `HyperAwareness11D.exists_unique_deepSets_params` — the two parameters are unique.
* `HyperAwareness11D.signEquivariant_offDiag_zero` — sign equivariance forces `M` diagonal.
* `HyperAwareness11D.hyperoctahedral_rigidity` — the two symmetries together force
  `M = a • 1`: **exactly one learnable parameter**, a global gain.
* `HyperAwareness11D.no_hyperoctahedral_channel_swap` — consequently no `B₁₁`-equivariant
  layer can mix two perception channels: hypercube symmetry annihilates all
  11-dimensional cross-channel processing.

The moral for the mission: *lossless* 11-dimensional processing (the `22`-unit optimum of
`Injectivity.lean`) and *fully symmetric* 11-dimensional processing are incompatible design
goals; genuine 11-dimensional perception must break the hyperoctahedral symmetry.
-/

open HyperAwareness11D

open Finset

noncomputable section

variable {n : ℕ}




/-! ## A two-point transitivity lemma for permutations -/


/-! ## Permutation equivariance -/

theorem HyperAwareness11D.exists_unique_deepSets_params(hn : 2 ≤ n) (M : Fin n → Fin n → ℝ)
    (h : PermEquivariant M) :
    ∃! p : ℝ × ℝ, ∀ i j, M i j = if i = j then p.1 else p.2 := by sorry
