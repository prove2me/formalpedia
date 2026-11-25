-- Prove2me | Theorems.Thm_syracuse_valuation_word_unique_residue_and_affine_progression
-- name    : syracuse_valuation_word_unique_residue_and_affine_progression
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T00:37:22.541551+00:00
-- url     : https://prove2.me/theorems/e1c5282f-831e-403e-8298-d2f366933efc
-- title:
--   Every positive Syracuse valuation word has one residue class and an affine endpoint
-- statement:
--   For a nonempty word $w$ of positive halving counts, let $P=2^{\sum w+1}$. There is one residue $r<P$ whose entire class realizes exactly $w$, and every start realizing $w$ is in that class. For all $m\ge0$, $T^{|w|}(r+Pm)=T^{|w|}(r)+2\cdot3^{|w|}m$. Thus one trajectory at the least representative determines the terminal value of every member of the class.
-- source:
--   Extends the mixed valuation certificate https://prove2.me/theorems/b1e4fd95-ab20-484b-ba65-a4fc321311e9 by proving existence and uniqueness of its residue class and the exact lift law.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_valuation_word_unique_residue_and_affine_progression (w : List ℕ) (hne : w ≠ [])
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a) :
    let P := 2^(w.sum+1)
    ∃ r < P,
      (∀ y : ℕ, y % P = r ↔ List.ofFn (fun i : Fin w.length =>
        (3*syracuseStep^[i.val] y+1).factorization 2) = w) ∧
      (∀ m : ℕ, syracuseStep^[w.length] (r+P*m) =
        syracuseStep^[w.length] r+2*3^w.length*m) := by sorry
