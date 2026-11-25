-- Prove2me | Theorems.Thm_syracuse_affine_word_replacement_gives_smaller_merging_start
-- name    : syracuse_affine_word_replacement_gives_smaller_merging_start
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T00:59:51.965989+00:00
-- url     : https://prove2.me/theorems/229fd775-98fa-4ce1-b43a-27bcba63a400
-- title:
--   A more favorable affine word gives a smaller start with the same Syracuse endpoint
-- statement:
--   Suppose an odd start $n$ realizes the valuation word $w$. A positive word $v$ of the same length $p$ and total valuation can replace it whenever $A(v)>A(w)$, $A(v)\equiv A(w)\pmod{3^p}$ and $A(v)+3^p\le A(w)+3^pn$. Then a positive odd start $k<n$ realizes $v$ and merges with the trajectory of $n$ at the common endpoint.
-- source:
--   A structural coalescence rule for https://prove2.me/missions/Collatz_Conjecture using syracuse_smaller_predecessor_iff_affine_interval.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Definitions.Def_collatzStepMap
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_affine_word_replacement_gives_smaller_merging_start (w v : List ℕ) (n : ℕ)
    (hn : ¬ 2 ∣ n)
    (hw : List.ofFn (fun i : Fin w.length =>
      (3*syracuseStep^[i.val] n+1).factorization 2) = w)
    (hv : ∀ a : ℕ, a ∈ v → 0 < a)
    (hlen : v.length=w.length) (hsum : v.sum=w.sum)
    (hgt : syracuseAffineConstant w < syracuseAffineConstant v)
    (hmod : syracuseAffineConstant v % 3^w.length = syracuseAffineConstant w % 3^w.length)
    (hroom : syracuseAffineConstant v+3^w.length ≤ syracuseAffineConstant w+3^w.length*n) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      syracuseStep^[w.length] n = syracuseStep^[v.length] k ∧
      List.ofFn (fun i : Fin v.length =>
        (3*syracuseStep^[i.val] k+1).factorization 2) = v := by sorry
