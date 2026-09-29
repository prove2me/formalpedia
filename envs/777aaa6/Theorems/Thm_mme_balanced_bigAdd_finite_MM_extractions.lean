-- Prove2me | Theorems.Thm_mme_balanced_bigAdd_finite_MM_extractions
-- name    : mme_balanced_bigAdd_finite_MM_extractions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T05:05:58.914904+00:00
-- url     : https://prove2.me/theorems/87df2153-8629-4469-b996-26995a79d8a1
-- title:
--   Balanced tensor power assembly from summandwise finite MM extractions
-- statement:
--   Let $X_1,\ldots,X_n$ be a nonempty finite family of order-three tensors, let $r,V$ be nonnegative integers, and let $L\ge0$. Suppose that every $X_p^{\otimes r}$ restricts to at least $L$ matrix-multiplication tensors and that every extracted tensor has dimension product exactly $V$. Put $R=nr$, and let $W$ be the multinomial number of length-$R$ words on $n$ letters in which every letter occurs exactly $r$ times. Then
--
--   $$
--   \left(\bigoplus_{p=1}^n X_p\right)^{\otimes R}
--   \;\ge_{\mathrm{Restrict}}\;
--   \bigoplus_{i=1}^k \langle a_i,b_i,c_i\rangle,
--   $$
--
--   where
--
--   $$
--   WL^n\le k,\qquad a_i b_i c_i=V^n\quad(1\le i\le k).
--   $$
--
--   This is the generic finite assembly lemma for an outer balanced type. Each balanced word supplies one copy of the product of all $n$ summandwise extractions, and the multinomial factor counts the modewise-disjoint outer words. The statement contains no asymptotic estimate and no C-tensor-specific hypothesis.
-- source:
--   The balanced-type expansion and distributive tensor-product assembly in V. Strassen's C-tensor value method, as used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271–272; https://doi.org/10.1016/S0747-7171(08)80013-2. The theorem isolates the underlying finite semiring and tensor-restriction step from the paper's C-tensor specialization.

import Mathlib.Data.Fintype.Card
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_tensor_rank

open MME BigOperators

universe u

theorem mme_balanced_bigAdd_finite_MM_extractions
    {K : Type u} [Field K]
    {n r V : ℕ} (X : Fin n → TensorObj K 3)
    (L : ℝ) (hn : 0 < n) (hL : 0 ≤ L)
    (hextract : ∀ p : Fin n,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((X p).kronPow r) ∧
        L ≤ (k : ℝ) ∧
        (∀ i, a i * b i * c i = V)) :
    let R : ℕ := n * r
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin n // ∀ p,
          Fintype.card {j // w j = p} = r}
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        ((TensorObj.bigAdd X).kronPow R) ∧
      (W : ℝ) * L ^ n ≤ (k : ℝ) ∧
      (∀ i, a i * b i * c i = V ^ n) := by
  sorry
