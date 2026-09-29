-- Prove2me | Theorems.Thm_mme_kron_power_concatenation_basis_transport
-- name    : mme_kron_power_concatenation_basis_transport
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:18:42.318869+00:00
-- url     : https://prove2.me/theorems/93b068f0-5775-4f2b-a446-a30e5eac280b
-- title:
--   Concatenating tensor powers preserves word bases and coordinates
-- statement:
--   Let $T$ be a three-mode tensor over a field $K$, and let $m,n\ge0$. There are invertible linear maps on its three mode spaces that identify the product $T^{\otimes m}\otimes T^{\otimes n}$ with $T^{\otimes(n+m)}$ and preserve the tensor itself. For any basis of any one mode, the corresponding map sends the tensor product of two word-basis vectors to the basis vector indexed by their concatenation:
--   $$F_i(b_w\otimes b_v)=b_{w\mathbin{\|}v}.$$
--   Concatenation is a bijection on word indices. Its first $m$ coordinates are exactly those of $w$, and its remaining $n$ coordinates are those of $v$. The statement includes empty powers. These coordinate identities allow filters on two separate powers to be transported to specified blocks of a single power.
-- source:
--   Associativity and the unit law for tensor products, with recursive word-basis transport.

import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_TypeGrading_kron

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_kron_power_concatenation_basis_transport
    {K : Type u} [Field K] (T : TensorObj K 3) (n m : ℕ) :
    ∃ F : ∀ i, (T.kronPow m).V i ⊗[K] (T.kronPow n).V i ≃ₗ[K]
        (T.kronPow (n + m)).V i,
      PiTensorProduct.map (fun i => (F i).toLinearMap)
        (interchange (T.kronPow m).t (T.kronPow n).t) = (T.kronPow (n + m)).t ∧
      ∀ (i : Fin 3) (ι : Type u) (b : Basis ι K (T.V i)),
        ∃ join : (PowIndex ι m × PowIndex ι n) ≃ PowIndex ι (n + m),
          (∀ w v, F i (kronPowModeBasis T i b m w ⊗ₜ[K] kronPowModeBasis T i b n v) =
            kronPowModeBasis T i b (n + m) (join (w, v))) ∧
          (∀ w v (r : Fin m), PowIndex.get (n + m) (join (w, v)) ⟨r.val, by omega⟩ =
            PowIndex.get m w r) ∧
          (∀ w v (r : Fin n), PowIndex.get (n + m) (join (w, v)) ⟨m + r.val, by omega⟩ =
            PowIndex.get n v r) := by sorry
