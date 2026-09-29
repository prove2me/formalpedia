-- Prove2me | Theorems.Thm_mme_kronFin_group_arbitrary_factors_by_fibers_iso
-- name    : mme_kronFin_group_arbitrary_factors_by_fibers_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:48:44.875307+00:00
-- url     : https://prove2.me/theorems/ebf0db62-2290-4027-9e58-8720316eca9f
-- title:
--   Regroup position-dependent Kronecker factors along finite fibers
-- statement:
--   Let $K$ be a field and let $(X_r)_{r<N}$ be an arbitrary position-dependent family of $d$-tensors. Partition the positions by a label map into $k$ fibers, and suppose the fiber of label $s$ is explicitly enumerated by a bijection $e_s:[\mu_s]\simeq\{r:\operatorname{label}(r)=s\}$. Then
--
--   $$
--   \bigotimes_{r<N}X_r
--     \cong
--   \bigotimes_{s<k}\left(\bigotimes_{j<\mu_s}X_{e_s(j)}\right).
--   $$
--
--   This isomorphism preserves every position-dependent factor and changes only the finite ordering and parenthesization. It is therefore suitable for grouping refined tensor blocks whose internal split labels vary within one coarse component fiber. Empty fibers and empty products are allowed.
-- source:
--   Elementary reindexing of a finite tensor product along the canonical disjoint-union equivalence of a function's fibers. This is the algebraic regrouping underlying the component standard form in Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 (PDF p.47 / printed p.46).

import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_kronFin_group_arbitrary_factors_by_fibers_iso
    {K : Type u} [Field K] {d N k : ℕ}
    (X : Fin N → TensorObj K d) (label : Fin N → Fin k)
    (multiplicity : Fin k → ℕ)
    (fiberEquiv : ∀ s : Fin k,
      Fin (multiplicity s) ≃ {r : Fin N // label r = s}) :
    TensorObj.Isomorphic
      (TensorObj.kronFin N X)
      (TensorObj.kronFin k (fun s ↦
        TensorObj.kronFin (multiplicity s) (fun j ↦
          X ((fiberEquiv s j).1)))) := by
  sorry
