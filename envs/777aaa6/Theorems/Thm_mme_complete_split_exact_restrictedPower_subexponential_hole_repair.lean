-- Prove2me | Theorems.Thm_mme_complete_split_exact_restrictedPower_subexponential_hole_repair
-- name    : mme_complete_split_exact_restrictedPower_subexponential_hole_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T05:30:39.570869+00:00
-- url     : https://prove2.me/theorems/f4a36b18-25de-4f1e-9151-882e3a0aadb1
-- title:
--   Literal exact-profile tensor repair from a subexponential number of three-mode holed copies
-- statement:
--   Let $T$ be a three-mode tensor over any field with chosen coordinate bases and complete fine-word labels at level $\ell$. For every real $\delta>0$, for all sufficiently large chunk counts $N$, there is a natural depth $h$ with
--
--   $$
--   \log(8^h)<\delta N.
--   $$
--
--   This depth is chosen independently of the exact complete-profile triple $\beta$. For each such triple, let $S=T^{\otimes N}[\beta,0]$ denote the literal simultaneous complete-profile restriction. In mode $i$, its coordinate basis is indexed by the original coordinate words satisfying that exact profile, and its block labels are the exact full-label words. There exist bases and block-label maps with those literal meanings: including a retained basis vector into the ambient tensor power gives its original power-basis vector, and its block-label word applies the original fine-word label at every chunk position.
--
--   Consider any $8^h$ copies of $S$, with sets $Q_{a,i}$ of missing full-label blocks in every copy and every mode. If
--
--   $$
--   8N\,|Q_{a,i}|\le |B_i|
--   \qquad\text{for every copy }a\text{ and mode }i,
--   $$
--
--   where $B_i$ is the exact full-label block type, then $S$ is a restriction of the direct sum of those holed copies. A holed copy is the actual coordinate projection of $S$ onto the complement of $Q_{a,i}$ in each of its three modes. The conclusion targets $S$ itself, not an abstract isomorphic source or an unproved all-label projection surrogate.
--
--   The result is for one exact-profile tensor term. It permits empty coordinate and block types and assumes no positive-tolerance transitivity. It does not produce the copies from hashing, prove their hole bounds, combine differently profiled terms, or assemble approximate interfaces from exact sectors. The logarithm is natural, and $N$ counts level-$\ell$ chunks, each containing $2^{\max(\ell-1,0)}$ fine positions.
-- source:
--   Term-level corollary of the exact-interface hole repair in More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definition 4.1 and Theorem 4.2. The underlying exact-domain chunk-shuffle argument is in Vassilevska Williams, Xu, Xu, Zhou, https://arxiv.org/abs/2307.07970v2, proof of restated Corollary 4.2, pp. 48–49. Uses the actual public CompleteSplit.restrictedPower, complete-word types, and modewise basis-label projections. The finite repair depth uses d=2N and 8^h source copies; its subexponential bound is a separate proved scalar estimate with the correct full-word width. This statement is not the full product-of-terms or positive-tolerance assembly theorem.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_modern_three_mode_projected_tensor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.ModernRepair PiTensorProduct Module
open scoped BigOperators Classical

universe u

set_option autoImplicit false

theorem mme_complete_split_exact_restrictedPower_subexponential_hole_repair
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) {ell : ℕ}
    (label : ∀ i, I i → CompleteWord ell) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      ∃ h : ℕ, Real.log ((8 ^ h : ℕ) : ℝ) < delta * N ∧
        ∀ beta : Fin 3 → Profile ell,
          let Coord := fun i ↦
            {w : PowIndex (I i) N // ApproxConsistent (label i) (beta i) 0 w}
          let Block := fun i ↦
            {w : PowIndex (CompleteWord ell) N // ApproxConsistent id (beta i) 0 w}
          let S := restrictedPower T b label beta 0 N
          let G := (T.kronPow N).basisAllAllowedGrading
            (fun i ↦ kronPowModeBasis T i (b i) N)
            (fun i ↦ ApproxConsistent (label i) (beta i) 0)
          ∃ B : ∀ i, Basis (Coord i) K (S.V i),
          ∃ blockLabel : ∀ i, Coord i → Block i,
            (∀ i w, (G.classOf i 0).subtype (B i w) =
              kronPowModeBasis T i (b i) N w.1) ∧
            (∀ i w, (blockLabel i w).1 =
              PowIndex.ofFun N (fun r ↦ label i (PowIndex.get N w.1 r))) ∧
            ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (Block i),
              (∀ a i, 8 * N * (holes a i).card ≤ Fintype.card (Block i)) →
              TensorObj.Restrict S
                (TensorObj.bigAdd (fun a ↦
                  projected S B blockLabel (fun i ↦ Finset.univ \ holes a i))) := by sorry
