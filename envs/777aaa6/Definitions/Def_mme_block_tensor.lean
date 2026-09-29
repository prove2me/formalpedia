-- Prove2me | Definitions.Def_mme_block_tensor
-- name    : mme_block_tensor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-31T22:59:04.809396+00:00
-- url     : https://prove2.me/theorems/6e5335b2-cd24-498c-818f-83c8231b2d3f
-- statement:
--   **Block tensors under a type grading** — the building block API for the abstract laser method.
--
--   For an order-$d$ tensor $T : \mathrm{TensorObj}\,K\,d$ with a $t$-way mode-wise direct-sum grading $G : T.\mathrm{TypeGrading}\,t$, every multi-type $\sigma : \mathrm{Fin}\,d \to \mathrm{Fin}\,t$ defines a **block projection** of $T.t$ onto the component $\bigotimes_i G.\mathrm{classOf}\,i\,(\sigma\,i)$.
--
--   This file provides two **sorry-free** building blocks:
--
--   1. `TensorObj.TypeGrading.blockProj G i α : T.V i →ₗ[K] G.classOf i α` — the per-mode projection onto the $\alpha$-th grading class, built from the linear equivalence `(⨁_α G.classOf i α) ≃ₗ[K] T.V i` granted by `G.is_internal i` (via `LinearEquiv.ofBijective ∘ DirectSum.coeLinearMap`).
--
--   2. `TensorObj.TypeGrading.blockTensor G σ` — the $\sigma$-block of $T.t$, obtained by applying `PiTensorProduct.map` mode-wise to the per-mode projections.
--
--   Both are `noncomputable` because the inverse of an internal direct sum is extracted via `Classical.choice`-style `LinearEquiv.ofBijective`. The block-decomposition theorem (`mme_graded_tensor_pow_block_decomp`) lives in a separate Theorem file.
--
--   **Reusability — the foundational API for laser-method block analysis.** Every laser-method paper's "block decompose, identify each block as MM, apply Salem–Spencer" workflow ultimately reduces to manipulations of these two functions. Stothers 2010, Vassilevska Williams 2012, Le Gall 2014, Alman–VW 2020 all factor through this abstraction.
-- source:
--   https://arxiv.org/abs/2212.11824

import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.PiTensorProduct
import Definitions.Def_mme_tensor_type_grading

/-! # Block tensors under a type grading

For an order-`d` tensor `T : TensorObj K d` equipped with a `t`-way mode-wise
direct-sum grading `G : T.TypeGrading t`, every multi-type
`σ : Fin d → Fin t` defines a **block projection** of `T.t` onto the
component `⨂ᵢ G.classOf i (σ i)`.

This file defines two `sorry`-free building blocks:

* `TensorObj.TypeGrading.blockProj G i α : T.V i →ₗ[K] G.classOf i α` — the
  per-mode projection onto the `α`-th grading class, built from the bijection
  `DirectSum.coeLinearMap (G.decomp i) : (⨁ α, G.classOf i α) ≃ₗ[K] T.V i`
  granted by `G.is_internal i`.

* `TensorObj.TypeGrading.blockTensor G σ : ⨂ᵢ G.classOf i (σ i)` — the
  `σ`-block of `T.t`, obtained by applying `PiTensorProduct.map` mode-wise
  to the per-mode projections.

Both are `noncomputable` because the inverse of an internal direct sum is
extracted via `Classical.choice`-style `LinearEquiv.ofBijective`. The
block-decomposition theorem (`mme_graded_tensor_pow_block_decomp`) lives in
`Theorems/`.

These two functions are the **only** API the abstract laser-method block
machinery needs from a TypeGrading; downstream theorems quantify over
`σ : Fin d → Fin t` and reason about the family of `blockTensor` projections.
-/

universe u

open PiTensorProduct DirectSum

namespace MME

namespace TensorObj.TypeGrading

variable {K : Type u} [Field K] {d : ℕ}
variable {T : TensorObj K d} {t : ℕ}

/-- The per-mode linear equivalence between `T.V i` and the internal direct sum
of its grading classes, granted by `G.is_internal i`. -/
noncomputable def modeLequiv (G : T.TypeGrading t) (i : Fin d) :
    (⨁ α, (G.decomp i α : Submodule K (T.V i))) ≃ₗ[K] T.V i :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (G.decomp i)) (G.is_internal i)

/-- The per-mode projection from `T.V i` onto the `α`-th grading class. Built from
`(modeLequiv G i).symm` followed by the `α`-th component of the direct sum. -/
noncomputable def blockProj (G : T.TypeGrading t) (i : Fin d) (α : Fin t) :
    T.V i →ₗ[K] G.classOf i α :=
  (DirectSum.component K (Fin t) (fun α => (G.decomp i α : Submodule K (T.V i))) α).comp
    (G.modeLequiv i).symm.toLinearMap

/-- The `σ`-block of `T.t` under the grading `G`: the projection of `T.t` onto
`⨂ᵢ G.classOf i (σ i)` obtained by tensoring the per-mode `blockProj`s. -/
noncomputable def blockTensor (G : T.TypeGrading t) (σ : Fin d → Fin t) :
    PiTensorProduct K (fun i => (G.classOf i (σ i) : Submodule K (T.V i))) :=
  PiTensorProduct.map (fun i => G.blockProj i (σ i)) T.t

end TensorObj.TypeGrading

end MME


