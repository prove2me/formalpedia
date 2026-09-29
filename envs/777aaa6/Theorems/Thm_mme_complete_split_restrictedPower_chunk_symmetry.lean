-- Prove2me | Theorems.Thm_mme_complete_split_restrictedPower_chunk_symmetry
-- name    : mme_complete_split_restrictedPower_chunk_symmetry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T04:24:54.157766+00:00
-- url     : https://prove2.me/theorems/9f9c091a-8449-4179-8973-00f7a3a4f324
-- title:
--   Common chunk permutations preserve the literal complete-profile tensor and exact empirical types
-- statement:
--   Let $T$ be a three-mode tensor over a field, with a chosen basis in each mode and a complete fine-word label for each basis vector. Fix three complete-split profiles $\beta$, a tolerance $\varepsilon\ge0$, a finite power $N$, and a common permutation $e$ of its constituent-factor positions. Write $S=T^{\otimes N}[\beta,\varepsilon]$ for the literal simultaneous complete-profile restriction, and let $\iota_i$ be its mode-space inclusions into $T^{\otimes N}$. Let $P_i$ be the canonical tensor-power basis permutation that sends a word $w$ to $w\circ e$.
--
--   There are actual modewise linear equivalences $\Psi_i$ of $S$ such that
--
--   $$
--   (\Psi_0\otimes\Psi_1\otimes\Psi_2)(S)=S,
--   \qquad
--   \iota_i\Psi_i=P_i\iota_i.
--   $$
--
--   The same permutation preserves every exact complete-word count:
--
--   $$
--   \operatorname{count}_{\sigma}(w\circ e)=\operatorname{count}_{\sigma}(w).
--   $$
--
--   Thus the shuffle preserves each exact empirical type as well as the approximate-profile restriction. This is an invariance statement; it does not assert transitivity or uniform fibers across different exact types inside an approximate-profile union.
--
--   **Formalization Note.** The theorem includes power zero under the existing empty-word convention. It assumes no tensor-symmetry or source-isomorphism hypothesis. For a canonical CW-square constituent, each permuted factor is one complete two-letter chunk; the fine letters inside it are not reversed.
-- source:
--   Derived finite algebraic interface for the chunk-permutation construction in Vassilevska Williams, Xu, Xu, Zhou, New Bounds for Matrix Multiplication: from Alpha to Omega, https://arxiv.org/abs/2307.07970v2, proof of Corollary4.2 (restated), pp48–49, and Property7.1. Complete-profile predicates and source tensor: Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 pp14–15 and Definition4.1 p15. This theorem formalizes only exact empirical-count invariance and actual tensor automorphisms. It is not the uniform-fiber or hole-repair theorem; those use exact profile domains. Reuses Proved position-permutation theorem81973b03-b8cd-4b32-805d-46fe1f4429c5 and recursive-basis theorem b68d576e-2831-46f8-a008-dcd00f83dc91.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  PiTensorProduct Module
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_restrictedPower_chunk_symmetry
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) {ell : ℕ}
    (label : ∀ i, I i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0)
    (N : ℕ) (e : Equiv.Perm (Fin N)) :
    let G := (T.kronPow N).basisAllAllowedGrading
      (fun i ↦ kronPowModeBasis T i (b i) N)
      (fun i ↦ ApproxConsistent (label i) (beta i) epsilon)
    (∀ (i : Fin 3) (w : PowIndex (I i) N) (sigma : CompleteWord ell),
      wordCount (label i) (PowIndex.reindex e w) sigma = wordCount (label i) w sigma) ∧
    ∃ Ψ : ∀ i, (restrictedPower T b label beta epsilon N).V i ≃ₗ[K]
        (restrictedPower T b label beta epsilon N).V i,
      PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap)
          (restrictedPower T b label beta epsilon N).t =
        (restrictedPower T b label beta epsilon N).t ∧
      ∀ i, (G.classOf i 0).subtype.comp (Ψ i).toLinearMap =
        (kronPowModePositionEquiv T i (b i) N e).toLinearMap.comp
          (G.classOf i 0).subtype := by sorry
