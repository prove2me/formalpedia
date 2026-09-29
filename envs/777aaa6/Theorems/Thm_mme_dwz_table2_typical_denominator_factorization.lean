-- Prove2me | Theorems.Thm_mme_dwz_table2_typical_denominator_factorization
-- name    : mme_dwz_table2_typical_denominator_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T12:54:57.47868+00:00
-- url     : https://prove2.me/theorems/261c81f4-e1dc-4158-8553-7f9dac66999c
-- title:
--   DWZ Lemma 6.7: exact Table 2 typical-denominator factorization
-- statement:
--   Let $S=10^{16}$ be the common integral scale of DWZ Table 2.  For every
--   $m\in\mathbb N$, there exists a coarse $Z$-word $K$ of length $Sm$ having
--   exact histogram $\alpha_Zm$.  If $B_{\mathrm{typ},K}$ is the family of
--   fine-pair words with exact histogram $\gamma m$ that coarsen pointwise to
--   $K$, then
--
--   $$
--   |B_{\mathrm{typ},K}|=
--   \prod_{k=0}^{4}\binom{\alpha_Z(k)m}
--     {(\gamma(p)m)_{\operatorname{coarse}(p)=k}}>0
--   $$
--
--   and
--
--   $$
--   \operatorname{Mult}(\gamma m)=
--   \operatorname{Mult}(\alpha_Zm)\,|B_{\mathrm{typ},K}|.
--   $$
--
--   Thus the abstract typical-word denominator in DWZ Lemma 6.7 is realized by
--   an actual word of the exact Table-2 type, with no rounding or divisibility
--   assumption.  The zero multiplier is included: both words are empty and the
--   typical family has cardinality one.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.4 and the denominator paragraph immediately after Equation (23), printed pp. 54-56 / PDF pp. 55-57, specialized to Section 6.3 Table 2.

import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_dwz_table2_gamma_pushforward

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_typical_denominator_factorization (m : ℕ) :
    ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
      let BtypicalK :=
        {small : Fin (MME.DWZTable2Counts.scale * m) → Fin 3 × Fin 3 //
          (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
          ∀ p, Fintype.card {t // small t = p} =
            MME.DWZTable2Counts.gamma p * m}
      (∀ k, Fintype.card {t // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
        Nat.card BtypicalK =
          ∏ k, Nat.multinomial Finset.univ
            (fun p : {p : Fin 3 × Fin 3 //
                MME.DWZTable2Counts.coarseOf p = k} =>
              MME.DWZTable2Counts.gamma p.1 * m) ∧
        0 < Nat.card BtypicalK ∧
        Nat.multinomial Finset.univ
            (fun p ↦ MME.DWZTable2Counts.gamma p * m) =
          Nat.multinomial Finset.univ
              (fun k ↦ MME.DWZTable2Counts.alphaZ k * m) *
            Nat.card BtypicalK := by
  sorry
