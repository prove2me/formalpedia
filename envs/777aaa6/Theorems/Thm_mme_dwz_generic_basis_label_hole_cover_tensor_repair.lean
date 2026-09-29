-- Prove2me | Theorems.Thm_mme_dwz_generic_basis_label_hole_cover_tensor_repair
-- name    : mme_dwz_generic_basis_label_hole_cover_tensor_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T15:22:05.627381+00:00
-- url     : https://prove2.me/theorems/91c76342-24f1-4894-9468-c663aa541533
-- title:
--   Generic basis-labelled exact-once tensor hole repair
-- statement:
--   Let $T$ be a three-mode tensor over an arbitrary field $K$. Give its $Z$-space a basis $\{e_i\}_{i\in I}$ and a label map $\lambda:I\to B$ into a finite nonempty set of available blocks. A finite nonempty shuffle family acts uniformly on $B$. Each shuffle is realized by modewise linear maps fixing $T$, and its $Z$ map permutes the basis in accordance with the block action.
--
--   For $s$ copies, let $A_t\subseteq B$ be the nonhole labels and let $T_t$ be the literal $Z$-coordinate projection of $T$ onto those labels, with the same ambient mode spaces. If $N,\ell>0$ and
--   \[|B|\le 2^{N\ell},\qquad \sum_{t=1}^{s}\frac{|A_t|}{|B|}\ge N\ell+1,\]
--   then there exist shuffles $g_t$, an owner $o(b)\in\{1,\ldots,s\}$ for every block, and explicit modewise linear maps $F_t$ such that $g_{o(b)}^{-1}b\in A_{o(b)}$. The $X$ and $Y$ maps are the chosen shuffle maps, and
--   \[F_t(T_t)=\sum_{b:o(b)=t}P_b(T),\qquad T\preceq\bigoplus_{t=1}^{s}T_t,\]
--   where $P_b$ is the singleton-label $Z$ projection. The construction assumes no owned-block realization certificate: the owner-selecting projections and these tensor identities are proved from the basis data. No characteristic restriction on $K$ is needed.
--
--   This is the finite linear-algebra step of the DWZ Hole Lemma for arbitrary block labels. Concrete standard-form shuffle invariance and block-label transport remain explicit hypotheses; no hardcoded table of component types is used.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S5.SS2, Section 5.2, Lemma 5.6 and its final exact-once zeroing/identification step; Definitions 5.4–5.5 and Claims 5.9–5.10 specify the labelled blocks and shuffles. Generic finite basis-labelled formulation of that construction, using the accepted uniform-cover theorem and singleton owner-projection identity.

import Theorems.Thm_mme_dwz_basis_label_owner_map_singleton
import Theorems.Thm_mme_dwz_hole_cover_exact_once_tensor_repair_poly
import Mathlib.Tactic

open MME Module PiTensorProduct
open MME.DWZComponentRestriction MME.DWZSquare
open scoped BigOperators
universe u v w z
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem mme_dwz_generic_basis_label_hole_cover_tensor_repair
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
    (N ell s : ℕ) (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy Block)
    (hcard : Fintype.card Block ≤ 2 ^ (N * ell))
    (hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
    let source : Fin s → TensorObj K 3 := fun t ↦
      { V := X.V
        t := PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label (copies t).nonholes)) X.t }
    ∃ (shuffles : Fin s → Shuffle) (owner : Block → Fin s)
        (f : ∀ t i, (source t).V i →ₗ[K] X.V i),
      (∀ block : Block,
        (system.move (shuffles (owner block))).symm block ∈
          (copies (owner block)).nonholes) ∧
      (∀ t, f t 0 = shuffleMap (shuffles t) 0) ∧
      (∀ t, f t 1 = shuffleMap (shuffles t) 1) ∧
      (∀ t, PiTensorProduct.map (f t) (source t).t =
        ∑ block : Block, if t = owner block then
          PiTensorProduct.map
            (Function.update (fun _ ↦ LinearMap.id) 2
              (basisLabelProjection b label {block})) X.t
        else 0) ∧
      TensorObj.Restrict X (TensorObj.bigAdd source) := by sorry
