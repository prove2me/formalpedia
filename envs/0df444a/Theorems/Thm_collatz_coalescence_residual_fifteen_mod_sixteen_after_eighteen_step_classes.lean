-- Prove2me | Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_eighteen_step_classes
-- name    : collatz_coalescence_residual_fifteen_mod_sixteen_after_eighteen_step_classes
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T07:21:45.106645+00:00
-- url     : https://prove2.me/theorems/be9c3278-d7aa-42c6-a8d9-c9b925b1847b
-- title:
--   Residual orbit mergers for 15 modulo 16 after eight eighteen-step predecessor classes
-- statement:
--   Let $C$ be the ordinary Collatz map. For a value $y$, let $m_{16}(y)$ be the least starting value reaching $y$ in at most 16 steps. Suppose $n\ge2{,}310{,}000$, $n\equiv15\pmod{16}$, and $n\bmod9$ is one of $0,1,3,6,7$. Assume that $m_{16}(C^t(n))\ge n$ for every $0\le t\le128$. Impose the earlier residue exclusions in the [parent theorem](https://prove2.me/theorems/3c628eed-a5a7-46d4-b122-633ac4d29a8f): exclude $10$ modulo $81$, $1743,1599$ modulo $2304$, and $2847,735,991,2527,3039,4575$ modulo $4608$.
--
--   In addition, exclude the eight residues
--   $$205,325,919,991,1000,1090,1171,2170\pmod{2187}.$$
--   For the remaining starts, show that some positive integer $k<n$ and some nonnegative indices $a,b$ satisfy $C^a(n)=C^b(k)$. The eight excluded classes admit an explicit smaller predecessor reaching $n$ in exactly eighteen steps.
-- source:
--   Residual case of https://prove2.me/theorems/3c628eed-a5a7-46d4-b122-633ac4d29a8f after removing the eight residue classes in collatz_smaller_predecessor_eighteen_steps_mod_2187.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_residual_fifteen_mod_sixteen_after_eighteen_step_classes (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575)
    (h2187 : n % 2187 ∉ [205, 325, 919, 991, 1000, 1090, 1171, 2170]) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
