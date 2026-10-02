-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter30_sum_eq_neg_self_of_sign_reversing_equiv
-- name    : ProofsInTheBook.Chapter30.sum_eq_neg_self_of_sign_reversing_equiv
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:29:21.051167+00:00
-- url     : https://prove2.me/theorems/15bc2c95-dc3a-4b94-a998-de20cc26e4f2
-- title:
--   A finite sign-reversing bijection negates the total sum
-- statement:
--   Let A be a finite type, let R be an additive commutative group, let $\tau:A\simeq A$ be a bijection, and let $w:A\to R$ satisfy $w(\tau x)=-w(x)$ for every x. Then $$\sum_{x\in A}w(x)=-\sum_{x\in A}w(x).$$ Neither an involution condition on the bijection nor a torsion-free assumption on R is required. The conclusion alone does not force the sum to be zero in the presence of 2-torsion.
-- source:
--   Exact repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L52. PathCountSystem hypotheses: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L435. Explicit scope limitation: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L578. Repository topic: “Lattice paths and determinants.” No edition-specific chapter mapping or geometric application is asserted.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter30
open ProofsInTheBook.Chapter30
open Matrix BigOperators

theorem ProofsInTheBook.Chapter30.sum_eq_neg_self_of_sign_reversing_equiv {α R : Type*} [Fintype α]
    [AddCommGroup R] (τ : α ≃ α) (w : α → R) (hw : ∀ x, w (τ x) = -w x) :
    (∑ x : α, w x) = -∑ x : α, w x := by sorry
