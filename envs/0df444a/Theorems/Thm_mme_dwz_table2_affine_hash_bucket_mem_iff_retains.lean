-- Prove2me | Theorems.Thm_mme_dwz_table2_affine_hash_bucket_mem_iff_retains
-- name    : mme_dwz_table2_affine_hash_bucket_mem_iff_retains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T02:14:56.096629+00:00
-- url     : https://prove2.me/theorems/d8090244-2d11-4c2b-86f6-461078e21ac1
-- title:
--   Canonical Table-2 bucket membership equals affine retention
-- statement:
--   Fix an odd prime $p$, a three-term-progression-free set $S\subseteq\{0,\ldots,\lfloor p/2\rfloor-1\}$, an ambient Table-2 family $A$, a word $a\in A$, and an affine state $q$. After embedding $S$ into $\mathbb Z/p\mathbb Z$, membership in the canonical affine bucket is equivalent to retention of the coarse $X$, $Y$, and $Z$ address words by that same state:
--
--   $$
--   a\in E_q\quad\Longleftrightarrow\quad
--   \operatorname{Retains}_q\bigl(X(a),Y(a),Z(a)\bigr).
--   $$
--
--   The level sum is exactly four at every coordinate. This exposes the semantic content of the public bucket needed to connect first-hash isolation with the common-state Claim-6.8 mass calculation.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, the asymmetric first hash in Section 6 preceding Claim 6.8 (printed pp. 48–52; PDF pp. 49–53); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_affine_hash_bucket
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label

open MME

set_option autoImplicit false

theorem mme_dwz_table2_affine_hash_bucket_mem_iff_retains
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (a : Fin (N + 1) → Fin 15) (ha : a ∈ A)
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    let castS : Finset (ZMod p) :=
      S.image (fun x : ℕ ↦ (x : ZMod p))
    a ∈ MME.dwzTable2AffineHashBucket S A q ↔
      MME.dwzAsymmetricAffineRetains (4 : ZMod p) castS
        (MME.dwzTable2CastX a) (MME.dwzTable2CastY a)
        (MME.dwzTable2CastZ a) q := by
  sorry
