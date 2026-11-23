-- Prove2me | Theorems.Thm_folding_components_in_code_implies_f_in_code
-- name    : folding_components_in_code_implies_f_in_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:07:04.1221+00:00
-- url     : https://prove2.me/theorems/243ae38c-883e-4d15-a423-00a653ce8b42
-- title:
--   folding components in code implies f in code: folding components in code implies f in code
-- statement:
--   The folding components in code implies f in code construction uses the folding components in code implies f in code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1107-L1128
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1107-L1128

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem folding_components_in_code_implies_f_in_code {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0)
    (f : F → F) (S : Finset F) (hS : S ⊆ D)
    (u' : Fin m → (pow_domain D m → F))
    (hu' : ∀ i, u' i ∈ reedSolomon (pow_domain D m) (d / m))
    (h_agree : ∀ i, ∀ z ∈ pow_domain S m, folding_component D m f i z =
      if h : z ∈ pow_domain D m then u' i ⟨z, h⟩ else 0) :
    ∃ u ∈ reedSolomon D d, ∀ (x : F) (hx : x ∈ S), u ⟨x, hS hx⟩ = f x := by sorry
