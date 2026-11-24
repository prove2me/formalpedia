-- Prove2me | Theorems.Thm_syracuse_mixed_valuation_prefix_descent_certificate
-- name    : syracuse_mixed_valuation_prefix_descent_certificate
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T17:38:54.46147+00:00
-- url     : https://prove2.me/theorems/b1e4fd95-ab20-484b-ba65-a4fc321311e9
-- title:
--   A mixed valuation prefix gives a Syracuse descent certificate with one congruence
-- statement:
--   Given a positive valuation word $w$, start $y$ and target $n$, set $B=3^{|w|}y+A(w)$ and $D=2^{\sum w}$. If $B\equiv D\pmod{2D}$ and $B<Dn$, the first $|w|$ Syracuse steps realize exactly $w$ and end at the odd value $B/D<n$. The word may contain different positive halving counts in any order.
-- source:
--   Generalizes the descent certificate https://prove2.me/theorems/a82c640b-5eab-4f94-a322-faa9bb9d60b7 to arbitrary positive halving counts.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_mixed_valuation_prefix_descent_certificate (w : List ℕ) (y n : ℕ)
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a)
    (hmod : (3^w.length*y+syracuseAffineConstant w) % 2^(w.sum+1) = 2^w.sum)
    (hbelow : 3^w.length*y+syracuseAffineConstant w < 2^w.sum*n) :
    syracuseStep^[w.length] y < n ∧
      syracuseStep^[w.length] y = (3^w.length*y+syracuseAffineConstant w)/2^w.sum ∧
      List.ofFn (fun i : Fin w.length =>
        (3*syracuseStep^[i.val] y+1).factorization 2) = w := by sorry
