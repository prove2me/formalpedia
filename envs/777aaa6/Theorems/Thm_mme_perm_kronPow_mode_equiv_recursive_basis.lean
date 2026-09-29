-- Prove2me | Theorems.Thm_mme_perm_kronPow_mode_equiv_recursive_basis
-- name    : mme_perm_kronPow_mode_equiv_recursive_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:48:20.060971+00:00
-- url     : https://prove2.me/theorems/f3523656-332d-4129-a59e-fd5c5248d54a
-- title:
--   The power-permutation equivalence preserves recursive product-basis words
-- statement:
--   Let $b$ be a basis of the $e^{-1}(i)$-th mode of an order-three tensor $T$. The same basis indexes mode $i$ after permuting the modes by $e$. For every recursive word $w$ of length $n$, the canonical equivalence between the corresponding modes of $(eT)^{\otimes n}$ and $T^{\otimes n}$ sends the product-basis vector indexed by $w$ to the product-basis vector with the same word:
--
--   $$
--   E_{e,T,n,i}igl(b_w^{(eT)^{\otimes n}}igr)=b_w^{T^{\otimes n}}.
--   $$
--
--   This exact word-level formula is the bridge needed to combine cyclic row routers with address projectors and forbidden-profile vanishing.
-- source:
--   Standard product-basis naturality under mode reindexing; formalization infrastructure for the q=6 Coppersmith-Winograd 121/211 rows.

import Definitions.Def_mme_perm_kronPow_mode_equiv
import Definitions.Def_mme_kron_pow_mode_word_basis

open MME MME.TensorObj MME.DWZComponentRestriction TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_perm_kronPow_mode_equiv_recursive_basis
    {K : Type u} [Field K]
    (e : Equiv.Perm (Fin 3)) (T : TensorObj K 3) (i : Fin 3)
    {I : Type u} (b : Basis I K (T.V (e.symm i))) :
    ∀ (n : ℕ) (w : PowIndex I n),
      permKronPowModeEquiv e T i n
          (kronPowModeBasis (TensorObj.permObj e T) i b n w) =
        kronPowModeBasis T (e.symm i) b n w := by
  sorry
