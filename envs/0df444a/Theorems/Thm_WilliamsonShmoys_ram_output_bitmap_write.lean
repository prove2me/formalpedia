-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_output_bitmap_write
-- name    : WilliamsonShmoys.ram_output_bitmap_write
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T08:34:37.034097+00:00
-- url     : https://prove2.me/theorems/03639a3e-ec4c-58c3-98d7-03f48537c118
-- title:
--   RAM writing of the output bitmap from the chosen copy
-- statement:
--   This RAM program writes the final answer of the planar independent-set PTAS into the output bitmap. It keeps the vertices of the chosen copy that are not deleted by its shift class.
--
--   Let a program $p$ contain, at position $o$, the 48-instruction program. On entry cell 32 holds $n$, cell 28 an even $\mathrm{LVB}\ge32+16n^2+16n$, cell 20 a copy index $c^\*$, and cell 22 an odd base $B$. The solver bit of vertex $v$ in the chosen copy is at $B+2v$, and the residue $m(v)$ at $\mathrm{LVB}+2v$. The program reaches $o+48$ within $26n+29$ operations, and for every $v<n$ the output cell defined by `planarRAMOutput` satisfies
--
--   $$\mathrm{nat}'(2+n^2+v)=\begin{cases}1,&\mathrm{bit}(B+2v)\ge1\ \text{and}\ m(v)\ne c^\*,\\ 0,&\text{otherwise.}\end{cases}$$
--
--   The output cells $2+n^2+v$ can coincide with the program's own registers when $n$ is small. The program therefore first writes the bits to the scratch cells $16(n^2+2+v)$ and a sentinel $16(n^2+1)$ to cell $16(n^2+1)$. It then copies the bits downwards with a loop that uses only cells $0$ and $1$. Every read address $16d\ge16(n^2+1)$ lies above every write address $d\le n^2+n+1$, so no value is overwritten before it is read.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (output of the best shifted solution)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_output_bitmap_write (p : List PlanarRAMInstruction) (o : ℕ)
    (hcode : CodeAt p o
    [natConst 0 0,
      natConst 2 1,
      natConst 4 2,
      natConst 36 16,
      natAdd 24 32 32,
      natAdd 18 28 24,
      natConst 30 0,
      natConst 6 0,
      natBranch 32 6 (o + 12) (o + 9),
      natAdd 30 30 32,
      natAdd 6 6 2,
      jump (o + 8),
      natAdd 26 30 0,
      natAdd 30 30 30,
      natAdd 30 30 30,
      natAdd 30 30 30,
      natAdd 30 30 30,
      natConst 8 32,
      natAdd 38 30 8,
      natAdd 10 28 0,
      natAdd 12 22 0,
      natBranch 18 10 (o + 34) (o + 22),
      natLoad 8 12,
      natBranch 2 8 (o + 24) (o + 29),
      natLoad 8 10,
      natBranch 8 20 (o + 26) (o + 27),
      natBranch 20 8 (o + 29) (o + 27),
      natStore 38 2,
      jump (o + 30),
      natStore 38 0,
      natAdd 10 10 4,
      natAdd 12 12 4,
      natAdd 38 38 36,
      jump (o + 21),
      natAdd 0 26 32,
      natAdd 0 0 2,
      natAdd 8 30 36,
      natStore 8 8,
      natAdd 1 0 0,
      natAdd 1 1 1,
      natAdd 1 1 1,
      natAdd 1 1 1,
      natLoad 1 1,
      natBranch 0 1 (o + 48) (o + 44),
      natStore 0 1,
      natConst 1 1,
      natSub 0 0 1,
      jump (o + 38)])
    (n LVB BB cc : ℕ) (hLe : LVB % 2 = 0) (hB : BB % 2 = 1) (hL : 32 + 16 * n * n + 16 * n ≤ LVB)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h32 : M 32 = n) (h28 : M 28 = LVB) (h20 : M 20 = cc) (h22 : M 22 = BB) :
    ∃ τ, τ ≤ 26 * n + 29 ∧ (planarRAMRun p ⟨o, M, R⟩ τ).pc = o + 48 ∧
      (∀ j, j < n → (planarRAMRun p ⟨o, M, R⟩ τ).natMem (2 + n * n + j) = (if 1 ≤ M (BB + 2 * j) ∧ M (LVB + 2 * j) ≠ cc then 1 else 0)) := by sorry
