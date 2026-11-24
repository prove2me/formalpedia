-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_halve_fragment
-- name    : WilliamsonShmoys.ram_halve_fragment
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T15:24:42.865913+00:00
-- url     : https://prove2.me/theorems/3decf909-29a7-4058-9fdf-9fc79318a254
-- title:
--   RAM fragment for halving with remainder
-- statement:
--   Let a program $p$ contain, at position $\mathrm{base}$, the 5-instruction loop that sets cell 9 to $0$ and then, while cell 10 $\le$ cell 8, subtracts cell 10 from cell 8 and adds cell 11 to cell 9. Started at $\mathrm{base}$ with $x$ in cell 8, $2$ in cell 10 and $1$ in cell 11, after exactly $4\lfloor x/2\rfloor+2$ operations the program counter is $\mathrm{base}+5$ and
--
--   $$\text{cell }8=x\bmod 2,\qquad \text{cell }9=\lfloor x/2\rfloor,$$
--
--   with all other cells unchanged. The instruction set has no division, so this is the basic decoding step for numbers built by repeated doubling.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction

theorem WilliamsonShmoys.ram_halve_fragment (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natConst 9 0, natBranch 10 8 (base + 2) (base + 5), natSub 8 8 10, natAdd 9 9 11, jump (base + 1)]) (s : PlanarRAMState) (hpc : s.pc = base) (h10 : s.natMem 10 = 2)
    (h11 : s.natMem 11 = 1) :
    let x := s.natMem 8
    let s' := planarRAMRun p s (4 * (x / 2) + 2)
    s'.pc = base + 5 ∧ s'.natMem 8 = x % 2 ∧ s'.natMem 9 = x / 2 ∧
      (∀ a, a ≠ 8 → a ≠ 9 → s'.natMem a = s.natMem a) ∧ s'.realMem = s.realMem := by sorry
