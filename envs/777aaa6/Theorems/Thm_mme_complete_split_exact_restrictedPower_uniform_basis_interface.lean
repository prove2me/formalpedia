-- Prove2me | Theorems.Thm_mme_complete_split_exact_restrictedPower_uniform_basis_interface
-- name    : mme_complete_split_exact_restrictedPower_uniform_basis_interface
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T04:47:01.789715+00:00
-- url     : https://prove2.me/theorems/6a036318-929c-4d2f-abbf-dee8a30da145
-- title:
--   Exact profile tensor: literal coordinate bases, full-label blocks, and common uniform shuffles
-- statement:
--   Let $T$ be a three-mode tensor over a field, with chosen coordinate bases and complete fine-word labels. Fix three exact complete-split profiles $\beta$ and a finite power $N$. Let $S=T^{\otimes N}[\beta,0]$ be the literal simultaneous profile restriction. In mode $i$, let $C_i$ be the original basis-coordinate words satisfying the exact profile, and let $L_i$ be the exact type of full-label words.
--
--   There are bases $B_i$ of the actual restricted mode spaces indexed by $C_i$, label maps $\lambda_i:C_i\to L_i$, and uniform block-shuffle systems $m_{e,i}$, indexed in all modes by the same $e\in S_N$. These data agree with the original coordinates: including $B_i(w)$ into the ambient power gives the original basis vector at $w$, and the underlying word of $\lambda_i(w)$ applies the original label at each position.
--
--   For every common permutation $e$, there are actual modewise linear equivalences $\Psi_{e,i}$ and coordinate-index maps $r_{e,i}$ such that
--
--   $$
--   (\Psi_{e,0}\otimes\Psi_{e,1}\otimes\Psi_{e,2})(S)=S,
--   $$
--
--   $$
--   r_{e,i}(w)=w\circ e^{-1},
--   \qquad
--   \Psi_{e,i}(B_i(w))=B_i(r_{e,i}(w)),
--   \qquad
--   \lambda_i(r_{e,i}(w))=m_{e,i}(\lambda_i(w)).
--   $$
--
--   The systems act by the same inverse-position permutation on full-label words and have the division-free uniform-fiber property. No source symmetry, basis coherence, or desired extraction is assumed.
--
--   This is the literal basis/label interface for repairing holes on one exact-profile tensor term. It includes empty retained coordinate types and power zero. It does not assert uniformity for a positive-tolerance union or carry out the product-of-terms repair assembly.
-- source:
--   Derived finite basis-level interface for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 pp14–15, Definition4.1 p15, and the exact-interface domain of Theorem4.2 p18. Chunk symmetries and exact-profile uniformity correspond to Vassilevska Williams, Xu, Xu, Zhou, https://arxiv.org/abs/2307.07970v2, Property7.1 and proof of restated Corollary4.2 pp48–49. Reuses Proved actual chunk symmetry9f9c091a-8449-4179-8973-00f7a3a4f324, exact-type uniformity e7262c1f-7b19-4d4d-b7ec-029d17c8aadc, and recursive basis action b68d576e-2831-46f8-a008-dcd00f83dc91. The retained basis is the ordinary basis-of-span construction with exact ambient inclusion values. This is not the whole hole-repair theorem or an approximate-union transitivity claim.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Mathlib.Data.Fintype.Perm

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.DWZSquare PiTensorProduct Module
open scoped Classical NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_exact_restrictedPower_uniform_basis_interface
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) {ell : ℕ}
    (label : ∀ i, I i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (N : ℕ) :
    let Coord := fun i ↦ {w : PowIndex (I i) N // ApproxConsistent (label i) (beta i) 0 w}
    let Block := fun i ↦ {w : PowIndex (CompleteWord ell) N // ApproxConsistent id (beta i) 0 w}
    let S := restrictedPower T b label beta 0 N
    let G := (T.kronPow N).basisAllAllowedGrading
      (fun i ↦ kronPowModeBasis T i (b i) N)
      (fun i ↦ ApproxConsistent (label i) (beta i) 0)
    ∃ B : ∀ i, Basis (Coord i) K (S.V i),
    ∃ blockLabel : ∀ i, Coord i → Block i,
    ∃ system : ∀ i, AvailableBlockShuffle (Block i) (Equiv.Perm (Fin N)),
      (∀ i w, (G.classOf i 0).subtype (B i w) = kronPowModeBasis T i (b i) N w.1) ∧
      (∀ i w, (blockLabel i w).1 =
        PowIndex.ofFun N (fun r ↦ label i (PowIndex.get N w.1 r))) ∧
      (∀ e i source, ((system i).move e source).1 = PowIndex.reindex e.symm source.1) ∧
      ∀ e : Equiv.Perm (Fin N),
        ∃ Ψ : ∀ i, S.V i ≃ₗ[K] S.V i,
        ∃ basisImage : ∀ i, Coord i → Coord i,
          PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap) S.t = S.t ∧
          (∀ i w, (basisImage i w).1 = PowIndex.reindex e.symm w.1) ∧
          (∀ i w, Ψ i (B i w) = B i (basisImage i w)) ∧
          (∀ i w, blockLabel i (basisImage i w) = (system i).move e (blockLabel i w)) := by sorry
