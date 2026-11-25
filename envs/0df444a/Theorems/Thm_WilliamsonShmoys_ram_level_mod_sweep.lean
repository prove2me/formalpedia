-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_level_mod_sweep
-- name    : WilliamsonShmoys.ram_level_mod_sweep
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T05:57:57.267649+00:00
-- url     : https://prove2.me/theorems/d703a737-528c-54aa-acd2-7a9664fb603d
-- title:
--   RAM sweep reducing BFS levels modulo k
-- statement:
--   This sweep turns the BFS labels into the residues used by Baker's shifting technique: it replaces every level label by the level modulo $k$.
--
--   Let a program $p$ contain, at position $h$, the 12-instruction loop over $w=0,\dots,n-1$ (cells 24 and 27). For each label it subtracts the offset $n+2$ (cell 17) and then reduces modulo $k$ (cell 16) by repeated subtraction. The labels sit at $L(j)=\mathrm{LVB}+2j$ with $\mathrm{LVB}\ge36$. Assume $k>0$, cells 13, 28, 11, 12, 19 hold $n$, $\mathrm{LVB}$, $1$, $0$, $2$, and every label satisfies $n+2\le L(j)\le 2n+2$. Then the program reaches $h+12$ within $(3n+9)n+3$ operations, and for every $j<n$
--
--   $$L'(j)=\bigl(L(j)-(n+2)\bigr)\bmod k .$$
--
--   All cells other than 22, 24, 27 and the label array are unchanged, as is the real memory. Applied after `ram_bfs_baker_levels`, where $L(j)=n+2+\mathrm{bakerLevel}(j)$ and $\mathrm{bakerLevel}(j)<n$, it produces $\mathrm{bakerLevel}(j)\bmod k$, the index of the shift class that deletes $j$.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, p. 270 (shifting classes)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_level_mod_sweep (p : List PlanarRAMInstruction) (h : ℕ)
    (hcode : CodeAt p h
    [natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (h + 12) (h + 3),
      natLoad 22 27,
      natSub 22 22 17,
      natBranch 16 22 (h + 6) (h + 8),
      natSub 22 22 16,
      jump (h + 5),
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (h + 2)])
    (n k LVB : ℕ) (hk : 0 < k) (hLVB : 36 ≤ LVB) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h16 : M 16 = k) (h17 : M 17 = n + 2) (h28 : M 28 = LVB) (h11 : M 11 = 1)
    (h12 : M 12 = 0) (h19 : M 19 = 2)
    (hb : ∀ j, j < n → n + 2 ≤ M (LVB + 2 * j) ∧ M (LVB + 2 * j) ≤ 2 * n + 2) :
    ∃ τ, τ ≤ (3 * n + 9) * n + 3 ∧
      (planarRAMRun p ⟨h, M, R⟩ τ).pc = h + 12 ∧
      (∀ j, j < n → (planarRAMRun p ⟨h, M, R⟩ τ).natMem (LVB + 2 * j) = (M (LVB + 2 * j) - (n + 2)) % k) ∧
      (∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → (∀ j, j < n → a ≠ LVB + 2 * j) →
        (planarRAMRun p ⟨h, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨h, M, R⟩ τ).realMem = R := by sorry
