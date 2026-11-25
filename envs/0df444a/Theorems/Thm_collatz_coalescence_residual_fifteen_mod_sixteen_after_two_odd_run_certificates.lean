-- Prove2me | Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_two_odd_run_certificates
-- name    : collatz_coalescence_residual_fifteen_mod_sixteen_after_two_odd_run_certificates
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-25T18:27:51.050698+00:00
-- url     : https://prove2.me/theorems/b4e49a00-b11f-5218-8898-364b587bdc78
-- title:
--   Remaining 15-mod-16 Collatz mergers after the two-run certificates
-- statement:
--   Retain every hypothesis of the [residual theorem after the initial odd-run certificates](https://prove2.me/theorems/121f3c7f-c265-4a8a-ac12-e2118a793952). For the ordinary Collatz map, define
--   $$
--   L=v_2(n+1),qquad q=(n+1)/2^L,qquad X=(3^Lq-1)/2,qquad
--   H=v_2(X+1),qquad Q=(X+1)/2^H,qquad W=3^H Q.
--   $$
--
--   Assume that none of the two-run certificate conditions below holds.
--
--   The certificate applies under any of these conditions.
--
--   - For a table row with shortening $d=2$, assume $Lle4$ and $Hge3$.
--   - For a table row with shortening $d=4$, assume $Lle7$ and $Hge5$.
--   - For a table row with shortening $d=6$, assume $Lle12$ and $Hge7$.
--
--   In each row, $W$ must have one of the given residues for its modulus.
--
--   | Shortening | Modulus | Residues |
--   | --- | --- | --- |
--   | 2 | 256 | 43 |
--   | 2 | 512 | 199, 363 |
--   | 2 | 1024 | 235, 395, 583 |
--   | 2 | 2048 | 263, 795, 839, 1163, 1175, 1515 |
--   | 2 | 4096 | 523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375 |
--   | 2 | 8192 | 1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799 |
--   | 4 | 16384 | 303, 2731, 6371 |
--   | 4 | 32768 | 12715, 18659, 20783, 23211 |
--   | 4 | 65536 | 1131, 8419, 15019, 25259, 26851, 30339, 37291, 39215, 45359, 47275, 60263 |
--   | 6 | 262144 | 4551, 43691, 198427, 208743 |
--
--   There is also an exit condition with no upper bound on the run lengths. It is
--   $$
--   exists sge0,qquad 2^smid W-1,qquad Wle2^s n.
--   $$
--
--   Prove that there are $k,a,binmathbb N$ such that
--   $$
--   0<k<n,qquad C^a(n)=C^b(k).
--   $$
--
--   This is the exact complement of the cases proved by the two-run certificate inside the existing residual.
-- source:
--   Exact complement within https://prove2.me/theorems/121f3c7f-c265-4a8a-ac12-e2118a793952 after applying collatz_two_odd_run_smaller_coalescence.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_coalescence_residual_fifteen_mod_sixteen_after_two_odd_run_certificates (n : ℕ)
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
      (P % 4 = 3 ∧ ∃ s : ℕ, 2 ≤ s ∧ 2^s ∣ 3*P-1 ∧ 3*3^L+2^s ≤ 2^(L+s))))
    (hsecond : let L := (n+1).factorization 2
      let q := (n+1)/2^L
      let X := (3^L*q-1)/2
      let H := (X+1).factorization 2
      let Q := (X+1)/2^H
      let W := 3^H*Q
      ¬ ((L ≤ 4 ∧ 3 ≤ H ∧
        (W % 256 ∈ ([43] : List ℕ) ∨
        W % 512 ∈ ([199, 363] : List ℕ) ∨
        W % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
        W % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
        W % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
        W % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ))) ∨
      (L ≤ 7 ∧ 5 ≤ H ∧
        (W % 16384 ∈ ([303, 2731, 6371] : List ℕ) ∨
        W % 32768 ∈ ([12715, 18659, 20783, 23211] : List ℕ) ∨
        W % 65536 ∈ ([1131, 8419, 15019, 25259, 26851, 30339, 37291, 39215, 45359, 47275, 60263] : List ℕ))) ∨
      (L ≤ 12 ∧ 7 ≤ H ∧
        (W % 262144 ∈ ([4551, 43691, 198427, 208743] : List ℕ))) ∨
      (∃ s : ℕ, 2^s ∣ W-1 ∧ W ≤ 2^s*(n)))) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
