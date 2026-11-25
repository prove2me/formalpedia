-- Prove2me | Theorems.Thm_collatz_two_odd_run_smaller_coalescence
-- name    : collatz_two_odd_run_smaller_coalescence
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:27:48.650461+00:00
-- url     : https://prove2.me/theorems/a1e61e1e-88b7-5c58-aff2-a3fddfe48535
-- title:
--   Smaller Collatz mergers with two odd runs and a power margin
-- statement:
--   Let $C$ be the ordinary Collatz map. Suppose $Lge4$, $q,Q>0$, and $Hge0$. Put $n=2^Lq-1$ and $W=3^H Q$, and assume
--   $$
--   3^Lq+1=2^{H+1}Q.
--   $$
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
--   Under any of these conditions, prove that
--   $$
--   exists k,a,binmathbb N,qquad 0<k<n,qquad C^a(n)=C^b(k).
--   $$
--
--   The run lengths count odd-step and immediate-halving pairs. An exit or merger is compared with the original start $n$.
-- source:
--   New second-run applications of the affine progression method of https://prove2.me/theorems/aa8d1225-2194-5505-af7a-fa130170bdfd for the exact residual https://prove2.me/theorems/121f3c7f-c265-4a8a-ac12-e2118a793952.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_two_odd_run_smaller_coalescence (L q H Q : ℕ) (hL : 4 ≤ L) (hq : 0 < q) (hQ : 0 < Q)
    (hbetween : 3^L*q+1 = 2^(H+1)*Q)
    (hcase : let W := 3^H*Q
      (L ≤ 4 ∧ 3 ≤ H ∧
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
      (∃ s : ℕ, 2^s ∣ W-1 ∧ W ≤ 2^s*(2^L*q-1))) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by sorry
