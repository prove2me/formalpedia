-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter22_rowLinearMixedCoefficient_eq_permanent
-- name    : ProofsInTheBook.Chapter22.rowLinearMixedCoefficient_eq_permanent
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:04:55.081756+00:00
-- url     : https://prove2.me/theorems/256ed68a-0980-4ebd-b7be-98dc36ead6a3
-- title:
--   The permutation mixed coefficient equals the permanent
-- statement:
--   For every real $n\times n$ matrix $A$, with $n\geq0$, the defined permutation mixed coefficient satisfies $$\sum_{\sigma\in S_n}\prod_{i=1}^n A_{i,\sigma(i)}=\operatorname{per}(A).$$ No sign or stochasticity hypothesis is required.
-- source:
--   Repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22.lean#L128. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture”, pp. 169–177 (https://doi.org/10.1007/978-3-662-57265-8_24). Auxiliary statements are cited to the repository and are not asserted to be separately numbered book theorems.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22
set_option autoImplicit true
open ProofsInTheBook.Chapter22
open Matrix
open ProofsInTheBook.PermanentConvexity

theorem ProofsInTheBook.Chapter22.rowLinearMixedCoefficient_eq_permanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearMixedCoefficient A = A.permanent := by sorry
