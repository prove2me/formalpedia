-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_baker_seg_input
-- name    : WilliamsonShmoys.ram_baker_seg_input
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T13:17:01.481003+00:00
-- url     : https://prove2.me/theorems/f666ae0c-f05d-5a57-9fd0-6c33e737a7d5
-- title:
--   Input relocation phase of the RAM Baker program
-- statement:
--   This is the first phase of the RAM program for Baker's planar PTAS. It moves the standard input into a sparse layout that leaves room for working registers.
--
--   Let a program $p$ contain the five accepted relocation fragments (`ram_pack_low_cells`, `ram_square_fragment`, `ram_spread_fragment`, `ram_unpack_low_cells`, `ram_real_spread_fragment`) at positions $0,12,19,28,79$, and three constant-setting instructions at $76$. Started on `planarRAMInput n k edge weight`, the program reaches position $95$ within $800k+8(n+1)^2+900$ operations. On arrival, cells $0$ and $32$ hold $n$, cell $34$ holds $k$, and cells $10,11,12$ hold $2,1,0$. Furthermore
--
--   $$\mathrm{nat}(36+2vn+2w)=[\mathrm{edge}(v,w)],\qquad \mathrm{real}(32+2v)=\mathrm{weight}(v)\qquad(v,w<n),$$
--
--   every natural cell $\ge48+2n^2$ is $0$, and every odd real cell $\ge n$ is $0$.
--
--   **Formalization Note.** Code placement uses `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (Baker's PTAS for planar weighted independent set)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_baker_seg_input (p : List PlanarRAMInstruction)
    (hc1 : CodeAt p 0 [natAdd 1 1 1, natAdd 1 1 2, natAdd 1 1 1, natAdd 1 1 3, natAdd 1 1 1, natAdd 1 1 4, natAdd 1 1 1, natAdd 1 1 5, natAdd 1 1 1, natAdd 1 1 6, natAdd 1 1 1, natAdd 1 1 7])
    (hc2 : CodeAt p 12 [natConst 4 1, natConst 2 2, natConst 3 0, natBranch 0 3 (12 + 7) (12 + 4), natAdd 2 2 0, natAdd 3 3 4, jump (12 + 3)])
    (hc3 : CodeAt p 19 [natConst 5 8, natConst 6 32, natBranch 2 5 (19 + 9) (19 + 3), natSub 2 2 4, natAdd 7 2 2, natAdd 7 7 6, natLoad 3 2, natStore 7 3, jump (19 + 2)])
    (hc4 : CodeAt p 28 [natConst 10 2, natConst 11 1, natConst 12 0, natAdd 32 0 12, natAdd 8 1 12, natConst 9 0, natBranch 10 8 (28 + 7) (28 + 10), natSub 8 8 10, natAdd 9 9 11, jump (28 + 6), natAdd 46 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 14) (28 + 17), natSub 8 8 10, natAdd 9 9 11, jump (28 + 13), natAdd 44 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 21) (28 + 24), natSub 8 8 10, natAdd 9 9 11, jump (28 + 20), natAdd 42 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 28) (28 + 31), natSub 8 8 10, natAdd 9 9 11, jump (28 + 27), natAdd 40 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 35) (28 + 38), natSub 8 8 10, natAdd 9 9 11, jump (28 + 34), natAdd 38 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (28 + 42) (28 + 45), natSub 8 8 10, natAdd 9 9 11, jump (28 + 41), natAdd 36 8 12, natAdd 8 9 12, natAdd 34 8 12])
    (hg : CodeAt p 76 [natConst 10 2, natConst 11 1, natConst 12 0])
    (hc5 : CodeAt p 79 [natAdd 2 0 12, natConst 6 32, natAdd 3 0 0, natAdd 3 3 11, realStore 3 0, natBranch 2 11 (79 + 12) (79 + 6), natSub 2 2 11, natAdd 7 2 2, natAdd 7 7 6, realLoad 0 2, realStore 7 0, jump (79 + 5), realLoad 0 3, realStore 6 0, realSub 0 0 0, realStore 3 0])
    (n k : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ) :
    ∃ τ, τ ≤ 800 * k + 8 * (n + 1) * (n + 1) + 900 ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).pc = 95 ∧
      (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 0 = n ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 32 = n ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 34 = k ∧
      (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 10 = 2 ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 11 = 1 ∧ (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem 12 = 0 ∧
      (∀ v w : Fin n, (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem (36 + 2 * v.val * n + 2 * w.val) = if edge v w then 1 else 0) ∧
      (∀ a, 48 + 2 * (n * n) ≤ a → (planarRAMRun p (planarRAMInput n k edge weight) τ).natMem a = 0) ∧
      (∀ v : Fin n, (planarRAMRun p (planarRAMInput n k edge weight) τ).realMem (32 + 2 * v.val) = weight v) ∧
      (∀ a, a % 2 = 1 → n ≤ a → (planarRAMRun p (planarRAMInput n k edge weight) τ).realMem a = 0) := by sorry
