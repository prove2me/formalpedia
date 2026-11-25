-- Prove2me | Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_trailing_ones_certificates
-- name    : collatz_coalescence_residual_fifteen_mod_sixteen_after_trailing_ones_certificates
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-25T18:12:06.596777+00:00
-- url     : https://prove2.me/theorems/121f3c7f-c265-4a8a-ac12-e2118a793952
-- title:
--   Remaining 15-mod-16 Collatz mergers after the initial odd-run certificates
-- statement:
--   Let $C$ be the ordinary Collatz map. Retain every hypothesis of the [residual theorem after the 23-step certificates](https://prove2.me/theorems/c60a76bf-0b48-569a-b7ba-2e5b56dcecf6). Define $L=v_2(n+1)$, $q=(n+1)/2^L$, and $P=3^Lq$.
--
--   Assume the following three conditions.
--
--   1. $P$ is not $1$ modulo $4$.
--   2. For every modulus in the table, the residue of $P$ lies outside the corresponding list.
--
--   | Modulus | Residues |
--   | --- | --- |
--   | 256 | 43 |
--   | 512 | 199, 363 |
--   | 1024 | 235, 395, 583 |
--   | 2048 | 263, 795, 839, 1163, 1175, 1515 |
--   | 4096 | 523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375 |
--   | 8192 | 1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799 |
--
--   3. The conjunction of $Pequiv3pmod4$ and the following existence statement fails.
--      $$
--      exists sge 2,qquad 2^smid 3P-1,qquad 3^{L+1}+2^sle 2^{L+s}.
--      $$
--
--   Prove that there exist $k,a,binmathbb N$ such that
--   $$
--   0<k<n,qquad C^a(n)=C^b(k).
--   $$
--
--   This is the remaining case of the earlier theorem after removing the three conditions which give smaller starts by the initial-odd-run certificates.
-- source:
--   Exact complement inside https://prove2.me/theorems/c60a76bf-0b48-569a-b7ba-2e5b56dcecf6 after applying collatz_trailing_ones_smaller_coalescence.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_coalescence_residual_fifteen_mod_sixteen_after_trailing_ones_certificates (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575)
    (h2187 : n % 2187 ∉ [205, 325, 919, 991, 1000, 1090, 1171, 2170])
    (h19683 : n % 19683 ∉ ([154, 433, 1384, 1663, 2134, 2548, 3268, 3364,
      3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517,
      6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187,
      12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376] : List ℕ))
    (hfirst : let L := (n+1).factorization 2
      let q := (n+1)/2^L
      let P := 3^L*q
      ¬ (P % 4 = 1 ∨
      P % 256 ∈ ([43] : List ℕ) ∨
      P % 512 ∈ ([199, 363] : List ℕ) ∨
      P % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
      P % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
      P % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
      P % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ) ∨
      (P % 4 = 3 ∧ ∃ s : ℕ, 2 ≤ s ∧ 2^s ∣ 3*P-1 ∧ 3*3^L+2^s ≤ 2^(L+s)))) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
