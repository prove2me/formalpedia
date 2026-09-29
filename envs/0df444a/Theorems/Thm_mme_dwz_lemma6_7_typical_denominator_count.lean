-- Prove2me | Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
-- name    : mme_dwz_lemma6_7_typical_denominator_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:30:50.787521+00:00
-- url     : https://prove2.me/theorems/59a722e1-fe1a-4b17-b2d8-07cfc0b8df44
-- title:
--   DWZ Lemma 6.7: exact typical-block denominator count
-- statement:
--   Let a finite fine-pair alphabet map to a finite coarse alphabet, and fix a coarse word K with prescribed histogram alphaZ. Prescribe a fine joint histogram gamma whose pushforward along the coarsening map is alphaZ. Then the number of fine words above K with exact histogram gamma is the product, over coarse labels k, of the multinomial coefficients for the gamma-counts in the fiber over k. Moreover, in exact division-free form,
--
--   $$\operatorname{Mult}(\gamma)=\operatorname{Mult}(\alpha_Z)\,|B_{\mathrm{typical},K}|.$$
--
--   For DWZ, fine labels are pairs $(k_l,k_r)$, the coarsening map is $(k_l,k_r)\mapsto k_l+k_r$, and the second equality is precisely the quotient of multinomials used to count the denominator immediately after Equation (23). No entropy asymptotic or compatibility probability is assumed.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.2, Definition 6.4 and the denominator count immediately after Equation (23), printed pp. 54-56 (PDF pp. 55-57).

import Mathlib

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_lemma6_7_typical_denominator_count
    {Position Pair Coarse : Type*}
    [Fintype Position] [DecidableEq Position]
    [Fintype Pair] [DecidableEq Pair]
    [Fintype Coarse] [DecidableEq Coarse]
    (coarseOf : Pair → Coarse) (K : Position → Coarse)
    (gamma : Pair → ℕ) (alphaZ : Coarse → ℕ)
    (hK : ∀ k,
      Fintype.card {t : Position // K t = k} = alphaZ k)
    (hPush : ∀ k,
      (∑ p : {p : Pair // coarseOf p = k}, gamma p.1) = alphaZ k) :
    let BtypicalK :=
      {small : Position → Pair //
        (∀ t, coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} = gamma p}
    let localCount :=
      ∏ k, Nat.multinomial Finset.univ
        (fun p : {p : Pair // coarseOf p = k} => gamma p.1)
    Nat.card BtypicalK = localCount ∧
      Nat.multinomial Finset.univ gamma =
        Nat.multinomial Finset.univ alphaZ * Nat.card BtypicalK := by sorry
