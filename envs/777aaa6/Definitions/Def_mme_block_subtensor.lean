-- Prove2me | Definitions.Def_mme_block_subtensor
-- name    : mme_block_subtensor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-01T00:26:57.62172+00:00
-- url     : https://prove2.me/theorems/d1faa6ba-540f-436d-9af6-862bbfab8d33
-- statement:
--   **Block subtensor as a `TensorObj`.**
--
--   `Def_mme_block_tensor` defines `G.blockTensor σ` as an element of `PiTensorProduct K (fun i => G.classOf i (σ i))` — a *raw tensor* on the grading-class submodules. This file wraps it into a full `TensorObj` so it can participate in `Restrict` / `Degenerates` / `bigAdd` relations like any other tensor object.
--
--   Provides:
--   - `instance classOf_finite` — finite-dimensionality of each grading class submodule (automatic from `Submodule.Module.Finite` since `T.V i` is finite-dimensional).
--   - `noncomputable def blockSubtensor σ : TensorObj K d` — the full TensorObj wrapping.
--
--   **Why this matters for reusability.** The 3 placeholder Layer-4 leaves (`mme_block_tensor_is_matMul`, `mme_independent_blocks_form_direct_sum_restrict`, `mme_laser_block_dimension_count`) have `True`-conclusion / `True`-hypothesis placeholders precisely because the "block as a TensorObj" wrapping wasn't formalised. This Def closes that gap: with `blockSubtensor` in hand, the refined Layer-4 statements can now reference `TensorObj.Restrict ... (G.blockSubtensor σ)` instead of vacuous placeholders.
--
--   **Reusability.** Every laser-method paper (CW 1990, Stothers 2010, VW 2012, Le Gall 2014, Alman-VW 2020) eventually needs to manipulate blocks as TensorObjs (for the Restrict / direct-sum machinery). This Def is the canonical wrapping; future Layer-4 refinement work builds on top.
-- source:
--   https://arxiv.org/abs/2212.11824

import Definitions.Def_mme_block_tensor

/-! # Block subtensor: the `σ`-block of a graded tensor as a `TensorObj`

`Def_mme_block_tensor` defines `G.blockTensor σ` as an element of
`PiTensorProduct K (fun i => G.classOf i (σ i))` — a *raw tensor* on the
grading-class submodules. This file wraps it into a full `TensorObj` so it
can participate in `Restrict` / `Degenerates` / `bigAdd` relations like any
other tensor object.

The wrapping requires that each grading class `G.classOf i α` is itself a
finite-dimensional `K`-module — which is automatic when `T.V i` is, because
finite-dim is closed under taking submodules in Mathlib. -/

universe u

namespace MME

variable {K : Type u} [Field K] {d t : ℕ}

namespace TensorObj.TypeGrading

variable {T : TensorObj K d} (G : T.TypeGrading t)

/-- Each grading class submodule of a finite-dimensional mode space is itself
finite-dimensional. -/
instance classOf_finite (i : Fin d) (α : Fin t) :
    Module.Finite K (G.classOf i α : Submodule K (T.V i)) :=
  inferInstance

/-- The `σ`-block of `T` packaged as a full `TensorObj K d` with mode spaces
`G.classOf i (σ i)` and the underlying tensor `G.blockTensor σ`. -/
noncomputable def blockSubtensor (σ : Fin d → Fin t) : TensorObj K d where
  V := fun i => (G.classOf i (σ i) : Submodule K (T.V i))
  t := G.blockTensor σ

end TensorObj.TypeGrading

end MME


