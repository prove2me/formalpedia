-- Prove2me | Theorems.Thm_syracuse_smaller_predecessor_iff_affine_interval
-- name    : syracuse_smaller_predecessor_iff_affine_interval
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T00:59:50.734501+00:00
-- url     : https://prove2.me/theorems/307c0325-c14a-4dc7-99df-83ac3dea0823
-- title:
--   Exact affine bounds for an odd endpoint to have a smaller prescribed predecessor
-- statement:
--   Fix an odd endpoint $y$, a bound $n$, and a finite word $w$ of positive halving counts. Put $F=2^{\sum w}y$, $C=A(w)$ and $M=3^{|w|}$. There is a positive odd $k<n$ that realizes exactly $w$ and ends at $y$ if and only if $F\equiv C\pmod M$ and $C+M\le F<C+Mn$. The predecessor is obtained by division of $F-C$ by $M$. The empty word is allowed.
-- source:
--   Combines https://prove2.me/theorems/8753c6d0-aa6f-482c-8741-cf84a6066f2f and https://prove2.me/theorems/afb53284-33e7-4fb3-b12f-cbbcb4d98334 into an inverse test on the endpoint.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Definitions.Def_collatzStepMap
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_smaller_predecessor_iff_affine_interval (w : List ℕ) (y n : ℕ)
    (hy : ¬ 2 ∣ y) (hpos : ∀ a : ℕ, a ∈ w → 0 < a) :
    let F := 2^w.sum*y
    let C := syracuseAffineConstant w
    let M := 3^w.length
    (F % M = C % M ∧ C+M ≤ F ∧ F < C+M*n) ↔
      ∃ k : ℕ, 0 < k ∧ k < n ∧ syracuseStep^[w.length] k = y ∧
        List.ofFn (fun i : Fin w.length =>
          (3*syracuseStep^[i.val] k+1).factorization 2) = w ∧ ¬ 2 ∣ k := by sorry
