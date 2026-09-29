-- Prove2me | Theorems.Thm_mme_MMObj_restrict_scalar_bigAdd_of_induced_matching
-- name    : mme_MMObj_restrict_scalar_bigAdd_of_induced_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:29:20.207522+00:00
-- url     : https://prove2.me/theorems/27fa65c5-796e-43fc-b8c3-98c2b93a4014
-- title:
--   Turn a support induced matching into a scalar direct-sum restriction
-- statement:
--   Let \(E\subseteq[H]^3\) be an induced matching in matrix-multiplication support: its \(X\)-, \(Y\)-, and \(Z\)-pair address maps are injective, and no mixed choice of three retained addresses forms a support triple unless all three come from the same member of \(E\).  Then, over any field \(K\), coordinate projection gives
--   \[
--   \bigoplus_{e\in E}\langle1,1,1\rangle
--   \ \le\ \langle H,H,H\rangle.
--   \]
--
--   The theorem is the exact tensor bridge from a combinatorial induced matching to independent scalar multiplication tensors.  Injectivity prevents two retained triples from sharing a variable, while the induced condition guarantees that projection introduces no off-diagonal support terms.
-- source:
--   Elementary coordinate-restriction realization of an induced matching in the support of the matrix-multiplication tensor.

import Definitions.Def_mme_tensor_rank
open MME BigOperators
universe u

theorem mme_MMObj_restrict_scalar_bigAdd_of_induced_matching
    {K : Type u} [Field K] (H : ℕ)
    (E : Finset (Fin H × Fin H × Fin H))
    (hx : Function.Injective
      (fun e : E => (e.1.1, e.1.2.1)))
    (hy : Function.Injective
      (fun e : E => (e.1.2.1, e.1.2.2)))
    (hz : Function.Injective
      (fun e : E => (e.1.2.2, e.1.1)))
    (hinduced : ∀ x y z : E,
      x.1.2.1 = y.1.2.1 →
      y.1.2.2 = z.1.2.2 →
      z.1.1 = x.1.1 →
      x = y ∧ y = z) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin E.card => MMObj K 1 1 1))
      (MMObj K H H H) := by sorry
