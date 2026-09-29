-- Prove2me | Theorems.Thm_syracuse_descent_residual_twentyseven_mod32_mod8192_excl8
-- name    : syracuse_descent_residual_twentyseven_mod32_mod8192_excl8
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-12T19:41:54.866503+00:00
-- url     : https://prove2.me/theorems/90428acc-af53-4bb4-8fb3-36a19c10aef5
-- title:
--   Remaining 27-mod-32 Syracuse descent classes after eight further progressions
-- statement:
--   Let $T(n)$ be the odd part of $3n+1$. Suppose $n$ is congruent to $27$ modulo $32$ and avoids the following classes: $59$ modulo $128$; $123$ and $219$ modulo $256$; $347$, $507$, and $923$ modulo $1024$; $1019$, $1435$, $1787$, $2203$, $2587$, $2907$, and $3675$ modulo $4096$; $539$, $1563$, $2075$, $3483$, $3835$, $4507$, $4859$, $5371$, $5723$, $6747$, and $7259$ modulo $8192$; and additionally $2331$, $3067$, $4091$, $4251$, $4955$, $5275$, $5787$, and $5979$ modulo $8192$. Prove that some iterate of $T$ is strictly smaller than $n$.
--
--   This is the open remainder of the $27$-mod-$32$ descent problem after removing eight further certified descent progressions. Both the starting value and the descent time are unbounded; no uniform bound on the number of steps is asserted.
--
--   **Formalization Note.** The imports use the existing `syracuseStep` definition. The final hypothesis block records exactly the eight newly removed classes.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; narrows syracuse_descent_residual_twentyseven_mod32_mod8192 (49dbc3ef-38df-4573-ac0c-ef1b9c35f45a) by the eight classes certified in the companion progression lemma. Method follows the Terras affine-step analysis; cf. J. Lagarias, The 3x+1 problem and its generalizations, Amer. Math. Monthly 92 (1985).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descent_residual_twentyseven_mod32_mod8192_excl8 (n : ℕ)
    (h : n % 32 = 27)
    (h128 : n % 128 ≠ 59)
    (h256 : n % 256 ≠ 123 ∧ n % 256 ≠ 219)
    (h1024 : n % 1024 ≠ 347 ∧ n % 1024 ≠ 507 ∧ n % 1024 ≠ 923)
    (h4096 : n % 4096 ≠ 1019 ∧ n % 4096 ≠ 1435 ∧ n % 4096 ≠ 1787 ∧
      n % 4096 ≠ 2203 ∧ n % 4096 ≠ 2587 ∧ n % 4096 ≠ 2907 ∧
      n % 4096 ≠ 3675)
    (h8192 : n % 8192 ≠ 539 ∧ n % 8192 ≠ 1563 ∧ n % 8192 ≠ 2075 ∧
      n % 8192 ≠ 3483 ∧ n % 8192 ≠ 3835 ∧ n % 8192 ≠ 4507 ∧
      n % 8192 ≠ 4859 ∧ n % 8192 ≠ 5371 ∧ n % 8192 ≠ 5723 ∧
      n % 8192 ≠ 6747 ∧ n % 8192 ≠ 7259)
    (h8192b : n % 8192 ≠ 2331 ∧ n % 8192 ≠ 3067 ∧ n % 8192 ≠ 4091 ∧
      n % 8192 ≠ 4251 ∧ n % 8192 ≠ 4955 ∧ n % 8192 ≠ 5275 ∧
      n % 8192 ≠ 5787 ∧ n % 8192 ≠ 5979) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry
