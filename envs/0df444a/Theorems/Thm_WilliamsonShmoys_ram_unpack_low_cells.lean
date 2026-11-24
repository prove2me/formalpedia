-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_unpack_low_cells
-- name    : WilliamsonShmoys.ram_unpack_low_cells
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T15:24:43.307342+00:00
-- url     : https://prove2.me/theorems/9b41dfee-ce3b-413c-b305-bfaa89c678f8
-- title:
--   RAM fragment restoring the packed low input cells
-- statement:
--   Let a program $p$ contain, at position $\mathrm{base}$, the 48-instruction fragment that copies cell 0 to cell 32 and then decodes cell 1 by six halving rounds (each a copy of `ram_halve_fragment`, followed by storing the remainder and moving the quotient back). Suppose cell 1 holds
--
--   $$P=64k+32b_2+16b_3+8b_4+4b_5+2b_6+b_7,\qquad b_i\in\{0,1\},$$
--
--   as produced by `ram_pack_low_cells`. Then within $12P+30$ operations the program reaches $\mathrm{base}+48$ with
--
--   $$\text{cell }32=\text{cell }0,\quad \text{cell }34=k,\quad \text{cell }(2c+32)=b_c\ (2\le c\le 7).$$
--
--   All cells other than the scratch cells $8$–$12$ and these targets are unchanged. Together with `ram_spread_fragment`, which moves cells $c\ge8$ to $2c+32$, this completes the relocation of the whole natural-memory input to the even cells $2c+32$.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction

theorem WilliamsonShmoys.ram_unpack_low_cells (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natConst 10 2, natConst 11 1, natConst 12 0, natAdd 32 0 12, natAdd 8 1 12, natConst 9 0, natBranch 10 8 (base + 7) (base + 10), natSub 8 8 10, natAdd 9 9 11, jump (base + 6), natAdd 46 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 14) (base + 17), natSub 8 8 10, natAdd 9 9 11, jump (base + 13), natAdd 44 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 21) (base + 24), natSub 8 8 10, natAdd 9 9 11, jump (base + 20), natAdd 42 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 28) (base + 31), natSub 8 8 10, natAdd 9 9 11, jump (base + 27), natAdd 40 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 35) (base + 38), natSub 8 8 10, natAdd 9 9 11, jump (base + 34), natAdd 38 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 42) (base + 45), natSub 8 8 10, natAdd 9 9 11, jump (base + 41), natAdd 36 8 12, natAdd 8 9 12, natAdd 34 8 12]) (s : PlanarRAMState) (hpc : s.pc = base)
    (k b2 b3 b4 b5 b6 b7 : ℕ) (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) (h4 : b4 ≤ 1) (h5 : b5 ≤ 1) (h6 : b6 ≤ 1)
    (h7 : b7 ≤ 1)
    (hP : s.natMem 1 = 64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) :
    ∃ τ, τ ≤ 12 * s.natMem 1 + 30 ∧
      (planarRAMRun p s τ).pc = base + 48 ∧
      (planarRAMRun p s τ).natMem 32 = s.natMem 0 ∧ (planarRAMRun p s τ).natMem 34 = k ∧
      (planarRAMRun p s τ).natMem 36 = b2 ∧ (planarRAMRun p s τ).natMem 38 = b3 ∧
      (planarRAMRun p s τ).natMem 40 = b4 ∧ (planarRAMRun p s τ).natMem 42 = b5 ∧
      (planarRAMRun p s τ).natMem 44 = b6 ∧ (planarRAMRun p s τ).natMem 46 = b7 ∧
      (∀ a, a ≠ 8 → a ≠ 9 → a ≠ 10 → a ≠ 11 → a ≠ 12 → a ≠ 32 → a ≠ 34 → a ≠ 36 → a ≠ 38 →
        a ≠ 40 → a ≠ 42 → a ≠ 44 → a ≠ 46 → (planarRAMRun p s τ).natMem a = s.natMem a) ∧
      (planarRAMRun p s τ).realMem = s.realMem := by sorry
