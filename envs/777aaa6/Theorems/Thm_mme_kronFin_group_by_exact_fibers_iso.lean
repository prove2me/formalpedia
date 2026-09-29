-- Prove2me | Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso
-- name    : mme_kronFin_group_by_exact_fibers_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:35:46.993413+00:00
-- url     : https://prove2.me/theorems/7f58c51e-d36a-46cc-b5d6-756d81527daa
-- title:
--   Group an ordered Kronecker product by exact label fibers
-- statement:
--   Let $K$ be a field, let $(X_s)_{s<k}$ be a finite family of $d$-tensors, and let $w:[N]\to[k]$ label each position of an ordered Kronecker product. Suppose the fiber of every label $s$ has exactly $\mu_s$ positions. Then
--
--   $$
--   \bigotimes_{r<N} X_{w(r)} \cong \bigotimes_{s<k} X_s^{\otimes \mu_s}.
--   $$
--
--   This tensor-object isomorphism is the finite regrouping operation used to put a typed tensor word into component-power standard form. It remains valid when $N=0$, $k=0$, or some multiplicities vanish; it does not replace tensor factors by dimensions or values.
-- source:
--   Elementary finite-product reindexing in the commutative isomorphism quotient of tensor objects; standard-form tensor products are used in Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 (PDF p.47 / printed p.46) and Section 6.3.

import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_kronFin_group_by_exact_fibers_iso
    {K : Type u} [Field K] {d N k : ℕ}
    (X : Fin k → TensorObj K d)
    (w : Fin N → Fin k) (multiplicity : Fin k → ℕ)
    (hcard : ∀ s : Fin k,
      Fintype.card {r : Fin N // w r = s} = multiplicity s) :
    TensorObj.Isomorphic
      (TensorObj.kronFin N (fun r ↦ X (w r)))
      (TensorObj.kronFin k (fun s ↦ (X s).kronPow (multiplicity s))) := by
  sorry
