-- Prove2me | Theorems.Thm_mme_dwz_generic_basis_label_multiple_copy_repair
-- name    : mme_dwz_generic_basis_label_multiple_copy_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T10:02:51.924649+00:00
-- url     : https://prove2.me/theorems/f31a59fb-ef0b-4d61-91f8-c7ada4f34fb2
-- title:
--   Multiple-copy tensor hole repair from aggregate nonhole mass
-- statement:
--   Let $X$ be a three-mode tensor over a field $K$, with a Z-mode basis $(b_i)_{i\in I}$ labelled by a finite nonempty block set $\mathcal B$. Suppose a finite nonempty shuffle family acts by block permutations, with each source block sent uniformly to every target block. Each shuffle is realized by modewise linear maps preserving $X$, permuting its Z basis compatibly with the block labels.
--
--   For subsets $A_1,\ldots,A_s\subseteq\mathcal B$, let $X_j$ be the literal broken copy obtained by projecting the Z mode onto the basis vectors whose labels lie in $A_j$, while leaving the X and Y modes unchanged. Set
--   $$
--   \eta_j=\frac{|A_j|}{|\mathcal B|}.
--   $$
--   Let $N,\ell>0$ and $r\geq0$ be integers. If
--   $$
--   |\mathcal B|\leq 2^{N\ell},
--   \qquad
--   r(N\ell+2)\leq\sum_{j=1}^{s}\eta_j,
--   $$
--   then
--   $$
--   \bigoplus_{j=1}^{s}X_j\longrightarrow X^{\oplus r}
--   $$
--   by a modewise linear tensor restriction.
--
--   In particular one may take $r=\lfloor\sum_j\eta_j/(N\ell+2)\rfloor$. This is the basis-labelled finite form of the multiple-copy repair step in DWZ Corollary 5.11. The original masks remain fixed, and source summands are not duplicated. Zero output copies and empty input families are included when the displayed budget holds.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.2, Corollary 5.11 and its proof, https://arxiv.org/html/2210.10173v5#S5.SS2 . Derived basis-labelled finite restriction version using the actual shuffle and exact-once owner maps; arbitrary integer output multiplicity, including zero.

import Theorems.Thm_mme_dwz_generic_basis_label_hole_cover_tensor_repair
import Theorems.Thm_mme_dwz_greedy_item_grouping
import Theorems.Thm_mme_bigAdd_list_flatten_isomorphic_nested
import Theorems.Thm_mme_bigAdd_list_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open MME Module PiTensorProduct
open MME.DWZComponentRestriction MME.DWZSquare
open scoped BigOperators
universe u v w z
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem mme_dwz_generic_basis_label_multiple_copy_repair
    {K : Type u} [Field K] (X : TensorObj K 3)
    {ι : Type z} {Block : Type w} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (b : Basis ι K (X.V 2)) (label : ι → Block)
    (system : AvailableBlockShuffle Block Shuffle)
    (shuffleMap : Shuffle → ∀ i, X.V i →ₗ[K] X.V i)
    (basisPerm : Shuffle → Equiv.Perm ι)
    (hZ : ∀ g i, shuffleMap g 2 (b i) = b (basisPerm g i))
    (hlabel : ∀ g i, label (basisPerm g i) = system.move g (label i))
    (hX : ∀ g, PiTensorProduct.map (shuffleMap g) X.t = X.t)
    (N ell s r : ℕ) (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy Block)
    (hcard : Fintype.card Block ≤ 2 ^ (N * ell))
    (hsum : (r : ℝ) * ((N * ell + 2 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
    let source : Fin s → TensorObj K 3 := fun t ↦
      { V := X.V
        t := PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label (copies t).nonholes)) X.t }
    TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin r ↦ X))
      (TensorObj.bigAdd source) := by sorry
