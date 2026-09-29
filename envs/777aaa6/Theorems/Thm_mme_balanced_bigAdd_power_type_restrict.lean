-- Prove2me | Theorems.Thm_mme_balanced_bigAdd_power_type_restrict
-- name    : mme_balanced_bigAdd_power_type_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T05:08:37.405686+00:00
-- url     : https://prove2.me/theorems/57020c2c-94a6-4441-8b6a-cb6af934d07f
-- title:
--   The balanced multinomial type restricts from a direct-sum tensor power
-- statement:
--   Let $X_1,\ldots,X_n$ be a nonempty finite family of order-three tensors, let $R=nr$, and let $W$ be the number of length-$R$ words on $n$ letters in which each letter occurs exactly $r$ times. Then
--
--   $$
--   \left(\bigoplus_{p=1}^n X_p\right)^{\otimes R}
--   \;\ge_{\mathrm{Restrict}}\;
--   \bigoplus_{w=1}^{W}\;\bigotimes_{p=1}^n X_p^{\otimes r}.
--   $$
--
--   Thus the balanced multinomial type is a modewise-disjoint restriction of the full tensor-power expansion. All $W$ balanced words become isomorphic copies of the same grouped product after commuting and associating Kronecker factors. The statement concerns only the outer balanced type and contains no matrix-multiplication extraction.
-- source:
--   The balanced-type expansion in V. Strassen's C-tensor value method, as used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271–272; https://doi.org/10.1016/S0747-7171(08)80013-2. This theorem isolates the finite multinomial direct-sum restriction underlying that argument.

import Mathlib.Data.Fintype.Card
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_tensor_quotient

open MME BigOperators

universe u

theorem mme_balanced_bigAdd_power_type_restrict
    {K : Type u} [Field K]
    {n r : ℕ} (X : Fin n → TensorObj K 3) (hn : 0 < n) :
    let R : ℕ := n * r
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin n // ∀ p,
          Fintype.card {j // w j = p} = r}
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin W =>
        TensorObj.kronFin n (fun p => (X p).kronPow r)))
      ((TensorObj.bigAdd X).kronPow R) := by
  sorry
