-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_square_fragment
-- name    : WilliamsonShmoys.ram_square_fragment
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T12:20:45.953799+00:00
-- url     : https://prove2.me/theorems/16299af3-7b89-4802-9c14-c0676744c3a9
-- title:
--   RAM fragment computing $2+n^2$
-- statement:
--   Let a program $p$ contain, at position $\mathrm{base}$, the 7-instruction fragment: set cell 4 to $1$, cell 2 to $2$ and cell 3 to $0$; then, while cell 0 exceeds cell 3, add cell 0 to cell 2 and cell 4 to cell 3. Started at $\mathrm{base}$ with $n$ in cell 0, after exactly $4n+4$ operations the program counter is $\mathrm{base}+7$ and
--
--   $$\text{cell }2=2+n^2,\qquad \text{cell }3=n,\qquad \text{cell }4=1,$$
--
--   with every other cell, natural or real, unchanged. In the mission's input layout, $2+n^2$ is the length $L$ of the natural-memory input (two header cells and the $n\times n$ adjacency table). The fragment uses only the cells $2,3,4$ freed by `ram_pack_low_cells`, and its correctness is proved by induction over the loop iterations.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`; cells are natural-memory cells.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction

theorem WilliamsonShmoys.ram_square_fragment (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natConst 4 1, natConst 2 2, natConst 3 0, natBranch 0 3 (base + 7) (base + 4), natAdd 2 2 0, natAdd 3 3 4, jump (base + 3)]) (s : PlanarRAMState) (hpc : s.pc = base) :
    let n := s.natMem 0
    let s' := planarRAMRun p s (4 * n + 4)
    s'.pc = base + 7 ∧ s'.natMem 2 = 2 + n * n ∧ s'.natMem 3 = n ∧ s'.natMem 4 = 1 ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 4 → s'.natMem a = s.natMem a) ∧ s'.realMem = s.realMem := by sorry
