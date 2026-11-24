-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_spread_fragment
-- name    : WilliamsonShmoys.ram_spread_fragment
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T12:20:45.094867+00:00
-- url     : https://prove2.me/theorems/5b4652f8-a866-4856-b87f-f11d25c9d2fe
-- title:
--   RAM fragment relocating the input table to even cells
-- statement:
--   Let a program $p$ contain, at position $\mathrm{base}$, the 9-instruction fragment that sets cell 5 to $8$ and cell 6 to $32$ and then, counting cell 2 down from $L$ while it exceeds $8$, copies cell $c$ to cell $2c+32$ by an indirect load and store through cells 3 and 7. Started at $\mathrm{base}$ with $L$ in cell 2 and $1$ in cell 4, after exactly $3+7\,(L-8)$ operations the program counter is $\mathrm{base}+9$ and, for every $c$ with $8\le c<L$,
--
--   $$\text{cell }(2c+32)=\text{original cell }c.$$
--
--   Every cell other than the scratch cells $2,3,5,6,7$ and the targets $2c+32$ is unchanged, and real memory is unchanged.
--
--   The copy runs from high addresses to low. Each target $2c+32$ is larger than every source still to be read, so no source is overwritten before it is copied, even though the copy is done in place. In the Baker shifting program this moves the input table onto even cells, leaving the odd cells to the sandboxed solver and the low cells to the host's registers.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`; cells are natural-memory cells.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction

theorem WilliamsonShmoys.ram_spread_fragment (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natConst 5 8, natConst 6 32, natBranch 2 5 (base + 9) (base + 3), natSub 2 2 4, natAdd 7 2 2, natAdd 7 7 6, natLoad 3 2, natStore 7 3, jump (base + 2)]) (s : PlanarRAMState) (hpc : s.pc = base) (h4 : s.natMem 4 = 1) :
    let L := s.natMem 2
    let s' := planarRAMRun p s (2 + 7 * (L - 8) + 1)
    s'.pc = base + 9 ∧
      (∀ c, 8 ≤ c → c < L → s'.natMem (2 * c + 32) = s.natMem c) ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 5 → a ≠ 6 → a ≠ 7 → (∀ c, 8 ≤ c → c < L → a ≠ 2 * c + 32) →
        s'.natMem a = s.natMem a) ∧
      s'.realMem = s.realMem := by sorry
