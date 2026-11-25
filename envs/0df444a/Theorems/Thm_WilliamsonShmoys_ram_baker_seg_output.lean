-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_baker_seg_output
-- name    : WilliamsonShmoys.ram_baker_seg_output
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T13:17:05.107258+00:00
-- url     : https://prove2.me/theorems/c03c61f7-02fa-50ce-90fc-43b9f4c76cc0
-- title:
--   Answer extraction phase of the RAM Baker program
-- statement:
--   This last phase reads the solver's answer and writes Baker's output. It runs from the sandbox exit $X$ and consists of `ram_best_copy_select` at $X$, a three-instruction glue block at $X+50$, and `ram_output_bitmap_write` at $X+53$.
--
--   Assume cells $32,34,28,40,42$ hold $n$, $k\ge1$, $\mathrm{LVB}$, $n$, $\mathrm{LVB}$ with $\mathrm{LVB}=16n^2+16n+48$. Then within $(16n+24)k+26n+52$ operations the program reaches $X+101$, and there is a copy $c^\*<k$ with $W_c\le W_{c^\*}$ for all $c<k$, where
--
--   $$W_c=\sum_{j<n}\bigl[\mathrm{bit}(5+2N^2+2cn+2j)\ge1,\ m(j)\ne c\bigr]\,\omega(32+2j)$$
--
--   with $N=kn$. Moreover, for every $v<n$, the output cell $2+n^2+v$ holds $1$ exactly when $\mathrm{bit}(5+2N^2+2c^\*n+2v)\ge1$ and $m(v)\ne c^\*$, and $0$ otherwise.
--
--   **Formalization Note.** Code placement uses `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (Baker's PTAS for planar weighted independent set)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_baker_seg_output (p : List PlanarRAMInstruction) (X : ℕ)
    (hca : CodeAt p X [natConst 0 0, natConst 2 1, natConst 4 2, natAdd 24 32 32, natAdd 18 28 24, natConst 26 0, natConst 6 0, natBranch 34 6 (X + 11) (X + 8), natAdd 26 26 32, natAdd 6 6 2, jump (X + 7), natConst 30 0, natConst 6 0, natBranch 26 6 (X + 17) (X + 14), natAdd 30 30 26, natAdd 6 6 2, jump (X + 13), natAdd 30 30 30, natConst 8 5, natAdd 14 30 8, natConst 6 0, natConst 20 0, natAdd 22 14 0, realZero 4, natBranch 34 6 (X + 50) (X + 25), realZero 2, natAdd 10 28 0, natConst 16 32, natAdd 12 14 0, natBranch 18 10 (X + 41) (X + 30), natLoad 8 12, natBranch 2 8 (X + 32) (X + 37), natLoad 8 10, natBranch 8 6 (X + 34) (X + 35), natBranch 6 8 (X + 37) (X + 35), realLoad 0 16, realAdd 2 2 0, natAdd 10 10 4, natAdd 12 12 4, natAdd 16 16 4, jump (X + 29), natBranch 6 0 (X + 43) (X + 42), realBranch 2 4 (X + 47) (X + 43), realZero 4, realAdd 4 4 2, natAdd 20 6 0, natAdd 22 14 0, natAdd 14 14 24, natAdd 6 6 2, jump (X + 24)])
    (hg4 : CodeAt p (X + 50) [natConst 0 0, natAdd 32 40 0, natAdd 28 42 0])
    (hcb : CodeAt p (X + 53) [natConst 0 0, natConst 2 1, natConst 4 2, natConst 36 16, natAdd 24 32 32, natAdd 18 28 24, natConst 30 0, natConst 6 0, natBranch 32 6 (X + 53 + 12) (X + 53 + 9), natAdd 30 30 32, natAdd 6 6 2, jump (X + 53 + 8), natAdd 26 30 0, natAdd 30 30 30, natAdd 30 30 30, natAdd 30 30 30, natAdd 30 30 30, natConst 8 32, natAdd 38 30 8, natAdd 10 28 0, natAdd 12 22 0, natBranch 18 10 (X + 53 + 34) (X + 53 + 22), natLoad 8 12, natBranch 2 8 (X + 53 + 24) (X + 53 + 29), natLoad 8 10, natBranch 8 20 (X + 53 + 26) (X + 53 + 27), natBranch 20 8 (X + 53 + 29) (X + 53 + 27), natStore 38 2, jump (X + 53 + 30), natStore 38 0, natAdd 10 10 4, natAdd 12 12 4, natAdd 38 38 36, jump (X + 53 + 21), natAdd 0 26 32, natAdd 0 0 2, natAdd 8 30 36, natStore 8 8, natAdd 1 0 0, natAdd 1 1 1, natAdd 1 1 1, natAdd 1 1 1, natLoad 1 1, natBranch 0 1 (X + 53 + 48) (X + 53 + 44), natStore 0 1, natConst 1 1, natSub 0 0 1, jump (X + 53 + 38)])
    (n k : ℕ) (hk : 0 < k) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = (16 * (n * n) + 16 * n + 48)) (h40 : M 40 = n) (h42 : M 42 = (16 * (n * n) + 16 * n + 48)) :
    ∃ τ, τ ≤ (16 * n + 24) * k + 26 * n + 52 ∧ (planarRAMRun p ⟨X, M, R⟩ τ).pc = X + 101 ∧
      ∃ cs, cs < k ∧ (∀ c', c' < k → (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * c' * n + 2 * j) ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * j) ≠ c' then R (32 + 2 * j) else 0) ≤ (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * cs * n + 2 * j) ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * j) ≠ cs then R (32 + 2 * j) else 0)) ∧
        ∀ v, v < n → (planarRAMRun p ⟨X, M, R⟩ τ).natMem (2 + n * n + v) =
          if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * cs * n + 2 * v) ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * v) ≠ cs then 1 else 0 := by sorry
