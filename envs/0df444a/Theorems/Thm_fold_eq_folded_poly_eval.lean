-- Prove2me | Theorems.Thm_fold_eq_folded_poly_eval
-- name    : fold_eq_folded_poly_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:17:39.476269+00:00
-- url     : https://prove2.me/theorems/ef11dac8-aba6-4434-acd3-43f85a1b93c8
-- title:
--   fold eq folded poly eval: fold eq folded poly eval
-- statement:
--   Key lemma: For a polynomial p and any z, the Fold operation on the evaluation
--   of p equals the evaluation of the folded polynomial at z.
--
--   More precisely, if f = p evaluated on D, and z ∈ D^m, then:
--     Fold(D, m, f, α)(z) = (folded_poly m p α).eval z
--
--   This is the core algebraic fact connecting polynomial folding to the Fold operation.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L280-L296
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L280-L296

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem fold_eq_folded_poly_eval (D : Finset F) (m : ℕ) (hm : m > 0)
    (p : Polynomial F) (alpha : F) (z : F) (hz : z ∈ pow_domain D m)
    (h_foldable : IsFoldable D m) :
    Fold D m (fun x ↦ p.eval x) alpha z = (folded_poly m p alpha).eval z := by sorry
