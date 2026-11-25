-- Prove2me | Theorems.Thm_collatz_trailing_ones_smaller_coalescence
-- name    : collatz_trailing_ones_smaller_coalescence
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:11:56.852804+00:00
-- url     : https://prove2.me/theorems/aa8d1225-2194-5505-af7a-fa130170bdfd
-- title:
--   Smaller Collatz mergers after an arbitrarily long initial odd run
-- statement:
--   Let $C$ be the ordinary Collatz map. For $Lge4$ and $q>0$, put $n=2^Lq-1$ and $P=3^Lq$. Assume at least one of the following.
--
--   1. The residue of $P$ modulo $4$ is $1$.
--   2. The residue of $P$ for some modulus in the table belongs to the corresponding list.
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
--   3. The residue of $P$ modulo $4$ is $3$, and there is an integer $sge2$ such that
--      $$
--      2^smid 3P-1,qquad 3^{L+1}+2^sle 2^{L+s}.
--      $$
--
--   Then there is a smaller positive integer whose orbit meets the orbit of $n$. In symbols,
--   $$
--   exists k,a,binmathbb N,qquad 0<k<n,qquad C^a(n)=C^b(k).
--   $$
--
--   The length $L$ is unrestricted. The residue guards allow the initial run of odd steps to have arbitrary length before the two trajectories are compared.
-- source:
--   New affine suffix collisions for https://prove2.me/theorems/c60a76bf-0b48-569a-b7ba-2e5b56dcecf6. Compatible case uses the arithmetic of https://prove2.me/theorems/79575c6c-8e26-4b1e-9f00-2022b29f942e and https://github.com/Sodelin/Collatz-Conjecture-Work/blob/main/proof-search/lemmas/L13_Refined_Mersenne_Child_Macros.md Section 2.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_trailing_ones_smaller_coalescence (L q : ℕ) (hL : 4 ≤ L) (hq : 0 < q)
    (hcase : let P := 3^L * q
      P % 4 = 1 ∨
      P % 256 ∈ ([43] : List ℕ) ∨
      P % 512 ∈ ([199, 363] : List ℕ) ∨
      P % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
      P % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
      P % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
      P % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ) ∨
      (P % 4 = 3 ∧ ∃ s : ℕ, 2 ≤ s ∧ 2^s ∣ 3*P-1 ∧ 3*3^L+2^s ≤ 2^(L+s))) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by sorry
