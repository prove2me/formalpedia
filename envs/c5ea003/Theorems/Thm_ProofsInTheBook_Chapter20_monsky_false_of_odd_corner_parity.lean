-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_monsky_false_of_odd_corner_parity
-- name    : ProofsInTheBook.Chapter20.monsky_false_of_odd_corner_parity
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:46:30.744255+00:00
-- url     : https://prove2.me/theorems/be3088a1-3dd6-4dfe-824e-7ad5def76327
-- title:
--   Equal areas and odd Monsky corner parity give a contradiction
-- statement:
--   Let n be an odd natural number and let $(a_i,b_i,c_i)\in(\mathbb R^2)^3$ be any family indexed by $i\in\{0,\ldots,n-1\}$. Suppose each triangle has area $|\det(b_i-a_i,c_i-a_i)|/2=1/n$, with the quotient formed in the rationals and embedded in the reals. Color all corners by the fixed Monsky coloring from the chosen extension of the rational 2-adic valuation. Let r_i count, with multiplicity, the red–green pairs among $(a_i,b_i),(b_i,c_i),(c_i,a_i)$. If $\sum_i r_i$ is odd, these hypotheses imply a contradiction. There is no covering, disjointness, or unit-square hypothesis; the odd corner-parity condition is supplied explicitly.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionSperner.lean#L24. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.”

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor

theorem ProofsInTheBook.Chapter20.monsky_false_of_odd_corner_parity
    {n : ℕ} (hn : Odd n) (tri : Fin n → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ))
    (harea : ∀ i, realTriangleArea (tri i).1 (tri i).2.1 (tri i).2.2 =
      (((1 : ℚ) / n : ℚ) : ℝ))
    (hodd : Odd (∑ i : Fin n, triangleLocalRGCount
      (realTwoAdicColor (tri i).1, realTwoAdicColor (tri i).2.1,
        realTwoAdicColor (tri i).2.2))) :
    False := by sorry
