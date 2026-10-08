-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_entropy_lower_le_log_choose
-- name    : ProofsInTheBook.Chapter03.entropy_lower_le_log_choose
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:27:35.750882+00:00
-- url     : https://prove2.me/theorems/c0f41868-c896-4465-8bcd-acc239a8293b
-- title:
--   An entropy lower bound for the logarithm of a binomial coefficient
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $0<k<n$, and define
--   $$H(n,k)=n\log n-k\log k-(n-k)\log(n-k).$$
--   Then
--   $$H(n,k)+\frac{\log n-\log k-\log(n-k)}2+\frac{\log(2\pi)}2-2\le\log\binom nk.$$
--   All logarithms are natural.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L525. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.entropy_lower_le_log_choose {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    entropyTerm n k
      + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
      + Real.log (2 * Real.pi) / 2 - 2
      ≤ Real.log (n.choose k) := by sorry
