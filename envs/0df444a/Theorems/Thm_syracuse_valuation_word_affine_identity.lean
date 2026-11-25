-- Prove2me | Theorems.Thm_syracuse_valuation_word_affine_identity
-- name    : syracuse_valuation_word_affine_identity
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T00:37:18.778065+00:00
-- url     : https://prove2.me/theorems/afb53284-33e7-4fb3-b12f-cbbcb4d98334
-- title:
--   The affine equation for the actual Syracuse valuation word
-- statement:
--   For a finite list $w$ of the actual exact halving counts of the Syracuse trajectory starting at $y$, the endpoint $z=T^{|w|}(y)$ satisfies $2^{\sum w}z=3^{|w|}y+A(w)$, with $A(w)$ the canonical affine constant. This is the converse direction to odd affine endpoint realization.
-- source:
--   Converse to https://prove2.me/theorems/8753c6d0-aa6f-482c-8741-cf84a6066f2f.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_valuation_word_affine_identity (w : List ℕ) (y : ℕ)
    (hword : List.ofFn (fun i : Fin w.length =>
      (3*syracuseStep^[i.val] y+1).factorization 2) = w) :
    2^w.sum * syracuseStep^[w.length] y = 3^w.length*y+syracuseAffineConstant w := by sorry
