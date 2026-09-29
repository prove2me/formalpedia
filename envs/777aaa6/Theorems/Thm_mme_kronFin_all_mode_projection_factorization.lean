-- Prove2me | Theorems.Thm_mme_kronFin_all_mode_projection_factorization
-- name    : mme_kronFin_all_mode_projection_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:24:48.228199+00:00
-- url     : https://prove2.me/theorems/835d8f83-b900-41dc-9eab-1cbc437f4b93
-- title:
--   All-mode product projections factor through the projected tensors
-- statement:
--   Let $K$ be a field and let $X_r$, for $r\in[n]=\{0,\ldots,n-1\}$,
--   be trilinear tensors. For each factor and mode $i\in\{0,1,2\}$, choose
--   a basis $b_{r,i}$ indexed by $I_{r,i}$ and a predicate $P_{r,i}$ on its
--   indices. Let $Y_r$ be the actual coordinate projection of $X_r$ onto the
--   span of the allowed basis vectors in each mode.
--
--   Write
--   $$
--   R=\bigotimes_{r<n}X_r,\qquad
--   S=\bigotimes_{r<n}Y_r,
--   $$
--   using the ordered finite-product convention. Let $B_i$ be the induced
--   product basis of $R$, indexed by words $w=(w_r)_{r<n}$. Define
--   $$
--   Q_i(w)\quad\Longleftrightarrow\quad
--   \forall r<n,\ P_{r,i}(w_r),
--   $$
--   and let $R[Q]$ be the simultaneous projection onto these coordinate
--   subspaces. Write $\pi_{Q,i}$ for the corresponding mode projections.
--
--   There are bases $\beta_{r,i}$ of the actual projected mode spaces,
--   indexed by $\{a\in I_{r,i}:P_{r,i}(a)\}$, whose inclusions into the
--   original spaces are exactly $b_{r,i}(a)$. Let $C_i$ denote the product
--   basis of $S$ induced by these bases. There are actual mode linear
--   equivalences
--   $$
--   F_i:(R[Q])_i\simeq_K S_i
--   $$
--   such that
--   $$
--   (F_0\otimes F_1\otimes F_2)R[Q]=S,
--   $$
--   and, for every word with all coordinates allowed,
--   $$
--   F_i\bigl(\pi_{Q,i}(B_i(w))\bigr)
--   =C_i\bigl((w_r)_{r<n}\bigr),
--   $$
--   where the coordinates on the right are regarded as elements of their
--   allowed-index subsets.
--
--   The conclusion includes zero-dimensional selected subspaces and $n=0$,
--   where the ordered empty product is the tensor unit. It proves the actual
--   factorization of a product-coordinate projection, not merely a dimension
--   identity or two-way tensor restriction. A concrete DWZ application must
--   still supply and identify its component bases and exact profile predicates.
-- source:
--   Derived basis-aware linear-algebra factorization underlying Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S5.SS1 , Section 5.1, Definition 5.2 (the product of prescribed-split component powers) and Definition 5.4 (componentwise exact-profile availability). This generic all-mode coordinate-projection lemma, including the empty product, is not separately numbered in the paper and does not by itself instantiate the canonical CW constituent/profile data.

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_complete_split_profile_projection
import Theorems.Thm_mme_kronFin_family_mode_map_selected_basis
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Basis.Submodule

open MME MME.TensorObj Module PiTensorProduct

universe u
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_kronFin_all_mode_projection_factorization
    {K : Type u} [Field K] {n : ℕ}
    (X : Fin n → TensorObj K 3)
    {I : Fin n → Fin 3 → Type u}
    (b : ∀ r i, Basis (I r i) K ((X r).V i))
    (P : ∀ r i, I r i → Prop) :
    let Y := fun r ↦ (X r).basisAllAllowedSubtensor (b r) (P r)
    let B := fun i ↦ kronFinModePiBasis n X i (fun r ↦ b r i)
    let G := (kronFin n X).basisAllAllowedGrading B (fun i w ↦ ∀ r, P r i (w r))
    ∃ β : ∀ r i, Basis {a : I r i // P r i a} K
        (((X r).basisAllAllowedGrading (b r) (P r)).classOf i 0),
      (∀ r i a, (β r i a : (X r).V i) = b r i a.val) ∧
      ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] (kronFin n Y).V i,
        PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (G.blockSubtensor (fun _ ↦ 0)).t = (kronFin n Y).t ∧
        ∀ i (w : ∀ r, I r i) (hw : ∀ r, P r i (w r)),
          F i (G.blockProj i 0 (B i w)) =
            kronFinModePiBasis n Y i (fun r ↦ β r i)
              (fun r ↦ ⟨w r, hw r⟩) := by sorry
