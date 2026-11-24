-- Prove2me | Theorems.Thm_syracuse_affine_prefix_realizes_odd_endpoint
-- name    : syracuse_affine_prefix_realizes_odd_endpoint
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T17:38:59.354809+00:00
-- url     : https://prove2.me/theorems/8753c6d0-aa6f-482c-8741-cf84a6066f2f
-- title:
--   An odd affine endpoint realizes the entire prescribed Syracuse valuation word
-- statement:
--   For a finite word $w$ of positive exact halving counts, write $A(w)$ for its Syracuse affine constant. If $z$ is odd and $2^{\sum w}z=3^{|w|}y+A(w)$, the first $|w|$ Syracuse steps from $y$ realize $w$ exactly and end at $z$. In particular $y$ is odd. The statement applies to finite paths with arbitrary endpoints.
-- source:
--   Finite-path version of the affine realization method. The earlier periodic realization is https://prove2.me/theorems/78b082d4-594c-4179-8e50-8e372a26c563.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_affine_prefix_realizes_odd_endpoint (w : List ℕ) (y z : ℕ)
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a) (hz : ¬ 2 ∣ z)
    (h : 2^w.sum*z = 3^w.length*y + syracuseAffineConstant w) :
    syracuseStep^[w.length] y = z ∧
    List.ofFn (fun i : Fin w.length =>
      (3*syracuseStep^[i.val] y+1).factorization 2) = w ∧
    ¬ 2 ∣ y := by sorry
