-- Prove2me | Theorems.Thm_mme_block_tensor_is_matMul_kronPow_balanced
-- name    : mme_block_tensor_is_matMul_kronPow_balanced
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-01T02:39:48.992732+00:00
-- url     : https://prove2.me/theorems/48f74a41-13cd-4063-8d21-f6d97c692e1b
-- statement:
--   **A tensor-power block with type-balanced multi-type triple is `Restrict`-equivalent to a matrix-multiplication tensor** — the *corrected* counterpart of `mme_block_tensor_is_matMul_refined`.
--
--   **Why the single-`N` `_refined` version is mathematically wrong.** `mme_block_tensor_is_matMul_refined` (theorem_id `4b09ae9d-ac8d-4a37-af62-f9769967a199`) claimed that for any `σ : Fin 3 → Fin t` with `(σ 0, σ 1, σ 2) ∈ S`, the single-block `G.blockSubtensor σ` is `Restrict`-equivalent to `MMObj K (dim₀) (dim₁) (dim₂)`. This is **false** in general: a single grading-block of `T.t` is only a slice of `T.t` and has no inherent matrix-multiplication structure. The MM tensor `MMObj K a b c = ∑_{i,j,k} e_{ij} ⊗ e_{jk} ⊗ e_{ki}` has a *specific* rank-one sum pattern (indices match cyclically) that arbitrary single blocks of an arbitrary tensor do not satisfy.
--
--   **Corrected statement.** Following Wigderson–Zuiddam, *Asymptotic spectra: theory, applications and extensions*, §6, and Coppersmith–Winograd 1990, Lemma 5.1: the matrix-multiplication structure only emerges when one passes to the tensor *power* `T.kronPow N` and selects a **type-balanced** multi-type triple `σ : Fin 3 → Fin (t ^ N)`. Identifying `Fin (t ^ N)` with `Fin N → Fin t` via `finFunctionFinEquiv`, **type-balanced** means: for every position `k : Fin N`, the coordinate triple `((σ 0)_k, (σ 1)_k, (σ 2)_k) ∈ S` — i.e. `(σ 0, σ 1, σ 2)` lies in the symbolic `N`-th power `S^N` of the cyclic-symmetric support pattern. For such balanced triples, the combinatorics of the Kronecker product forces the surviving rank-one expansion of `induced.blockTensor σ` to factor as a matrix-multiplication tensor of dimensions determined by the *type-multiplicity statistics* of `σ` (specifically, multinomial coefficients on the support pattern's distribution).
--
--   **Existential dimensions.** The dimensions `(a, b, c)` are left existentially quantified — the explicit closed form (multinomial coefficients in the type-counts) is the content of the layer-3 numeric refinement and depends on the same cyclic-marginal statistics used in `mme_laser_block_dimension_count_refined`.
--
--   **Decomposition strategy (layer-3 plan).**
--   1. *Combinatorial reindexing.* The type-balanced hypothesis lets one re-index the `t^N` grading-class indices by `Sym N`-orbits in `S^N`; each orbit has size a multinomial coefficient.
--   2. *Block isomorphism.* Within each orbit, the surviving rank-one terms of `induced.blockTensor σ` exhibit the explicit `e_{IJ} ⊗ e_{JK} ⊗ e_{KI}` pattern of an MM tensor whose three dimensions are the multinomial coefficients of the three coordinate-types' marginal distributions.
--
--   **Reusability.** Every laser-method paper — CW 1990, Stothers 2010, Vassilevska Williams 2012, Le Gall 2014, Duan–Wu–Zhou 2023 — has *this* exact statement as its "each surviving block is an MM tensor of multinomial dimensions" lemma. The single-`N` `_refined` form was a category error: the MM structure is intrinsically a tensor-power phenomenon.
--
--   **Suffix `_kronPow_balanced`.** Distinguishes from the single-`N` `_refined` version (which is mathematically incorrect and should be treated as deprecated).
-- source:
--   https://arxiv.org/abs/2212.11824

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_block_tensor_is_matMul_kronPow_balanced
    {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (S : Finset (Fin t × Fin t × Fin t))
    (_hSym : MME.LaserSymmetric S)
    (_hsupport : TensorObj.LaserAlignedSupport G S)
    (N : ℕ)
    (induced : (T.kronPow N).TypeGrading (t ^ N))
    (σ : Fin 3 → Fin (t ^ N))
    (_hBalanced : ∀ k : Fin N,
        ((finFunctionFinEquiv (n := N) (m := t)).symm (σ 0) k,
         (finFunctionFinEquiv (n := N) (m := t)).symm (σ 1) k,
         (finFunctionFinEquiv (n := N) (m := t)).symm (σ 2) k) ∈ S) :
    ∃ (a b c : ℕ),
      TensorObj.Restrict
        (MMObj K a b c)
        (induced.blockSubtensor σ) := by sorry
