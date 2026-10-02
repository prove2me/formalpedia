-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_prod_lPowerFreeParts_dvd_factorial
-- name    : ProofsInTheBook.Chapter03.prod_lPowerFreeParts_dvd_factorial
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:27:40.573169+00:00
-- url     : https://prove2.me/theorems/8bb814cb-b90d-4280-a594-a92fc8e4a573
-- title:
--   Power-free parts divide k! when a binomial coefficient is an lth power
-- statement:
--   Let $n,k,l,m\in\mathbb N$ satisfy $4\le k$, $2k\le n$, $2\le l$, and $\binom nk=m^l$. For a positive integer $u$, write $A_l(u)=\prod_{p\mid u}p^{v_p(u)\bmod l}$, where the product is over prime divisors and $v_p(u)$ is the exponent of $p$ in $u$. Then
--   $$\prod_{j=0}^{k-1}A_l(n-j)\mid k!.$$
--   All arguments $n-j$ in the product are positive under the hypotheses.
--
--   This is a conditional divisibility step for the perfect-power contradiction; it does not itself assert that the assumed perfect power exists.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L5156. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.prod_lPowerFreeParts_dvd_factorial
    {n k l m : ℕ} (_hk : 4 ≤ k) (hn : 2 * k ≤ n) (hl : 2 ≤ l)
    (h_eq : n.choose k = m ^ l) :
    (∏ j ∈ Finset.range k, lPowerFreePart l (n - j)) ∣ k ! := by sorry
