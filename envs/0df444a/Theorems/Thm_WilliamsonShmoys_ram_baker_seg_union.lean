-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_baker_seg_union
-- name    : WilliamsonShmoys.ram_baker_seg_union
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T13:17:22.777341+00:00
-- url     : https://prove2.me/theorems/d360de02-4356-4dc6-95a2-8f6f63aabf5e
-- title:
--   Union-instance construction phase: solver input in the odd sandbox cells
-- statement:
--   This phase builds the input of the single solver call and prepares the sandbox. It runs from position $207$ to $283$ and consists of `ram_union_instance_build` and a 22-instruction glue block.
--
--   Assume cells $32,34,28$ hold $n$, $k\ge1$ and $\mathrm{LVB}=16n^2+16n+48$, and that all odd natural and real cells are $0$. Then within $((11n+20)n+12)k+4n+50$ operations the program reaches $283$ in a state $s'$ with
--
--   $$\texttt{SandboxOddRel}\ 2\ \bigl(\texttt{planarRAMInput}\ (kn)\ (3k)\ \mathrm{edge}'\ \omega'\bigr)\ s' ,$$
--
--   where $\mathrm{edge}'$ and $\omega'$ are the masked disjoint-union edge table and weights read from the residues at $\mathrm{LVB}+2v$, the edge bits at $36+2vn+2w$ and the weights at real $32+2v$. The glue block recomputes $\mathrm{LVB}$ into cell $28$, copies $n$ and $\mathrm{LVB}$ into cells $40,42$, and sets cell $2$ to $1$. Even cells $\ge44$ and even real cells $\ne0$ are preserved.
--
--   **Formalization Note.** `SandboxOddRel` is from `Def_WilliamsonShmoys_RAMSandboxOdd`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (Baker's PTAS for planar weighted independent set)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Definitions.Def_WilliamsonShmoys_RAMSandboxOdd

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_baker_seg_union (p : List PlanarRAMInstruction)
    (hc : CodeAt p 207 [natConst 0 0, natConst 2 1, natConst 4 2, natAdd 26 32 32, natAdd 30 28 26, natConst 8 0, natConst 6 0, natBranch 34 6 (207 + 11) (207 + 8), natAdd 8 8 32, natAdd 6 6 2, jump (207 + 7), natAdd 10 8 8, natSub 24 10 26, natConst 10 1, natStore 10 8, natAdd 8 34 34, natAdd 8 8 34, natConst 10 3, natStore 10 8, natConst 6 0, natConst 18 5, natConst 22 1, natBranch 34 6 (207 + 54) (207 + 23), natAdd 12 28 0, natConst 20 32, natConst 16 36, natBranch 30 12 (207 + 51) (207 + 27), natLoad 8 12, natBranch 8 6 (207 + 29) (207 + 30), natBranch 6 8 (207 + 44) (207 + 30), realLoad 0 20, realStore 22 0, natAdd 14 28 0, natBranch 30 14 (207 + 46) (207 + 34), natLoad 10 14, natBranch 10 6 (207 + 36) (207 + 37), natBranch 6 10 (207 + 40) (207 + 37), natLoad 10 16, natBranch 2 10 (207 + 39) (207 + 40), natStore 18 2, natAdd 14 14 4, natAdd 16 16 4, natAdd 18 18 4, jump (207 + 33), natAdd 16 16 26, natAdd 18 18 26, natAdd 18 18 24, natAdd 12 12 4, natAdd 20 20 4, natAdd 22 22 4, jump (207 + 26), natAdd 18 18 26, natAdd 6 6 2, jump (207 + 22)])
    (hg3 : CodeAt p 261 [natConst 0 0, natConst 4 0, natConst 6 0, natConst 8 1, natBranch 32 6 (261 + 8) (261 + 5), natAdd 4 4 32, natAdd 6 6 8, jump (261 + 4), natAdd 28 4 4, natAdd 28 28 28, natAdd 28 28 28, natAdd 28 28 28, natAdd 6 32 32, natAdd 6 6 6, natAdd 6 6 6, natAdd 6 6 6, natAdd 28 28 6, natConst 6 48, natAdd 28 28 6, natAdd 40 32 0, natAdd 42 28 0, natConst 2 1])
    (n k : ℕ) (hk : 0 < k) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = (16 * (n * n) + 16 * n + 48))
    (hodd : ∀ a, a % 2 = 1 → M a = 0) (hRodd : ∀ a, a % 2 = 1 → R a = 0) :
    ∃ τ, τ ≤ ((11 * n + 20) * n + 12) * k + 4 * n + 50 ∧ (planarRAMRun p ⟨207, M, R⟩ τ).pc = 283 ∧
      SandboxOddRel 2 (planarRAMInput (k * n) (3 * k) (fun x y : Fin (k * n) => decide (x.val / n = y.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n ∧ M ((16 * (n * n) + 16 * n + 48) + 2 * (y.val % n)) ≠ x.val / n ∧ 1 ≤ M (36 + 2 * (x.val % n) * n + 2 * (y.val % n)))) (fun x : Fin (k * n) => if M ((16 * (n * n) + 16 * n + 48) + 2 * (x.val % n)) ≠ x.val / n then R (32 + 2 * (x.val % n)) else 0)) (planarRAMRun p ⟨207, M, R⟩ τ) ∧
      (planarRAMRun p ⟨207, M, R⟩ τ).natMem 32 = n ∧ (planarRAMRun p ⟨207, M, R⟩ τ).natMem 34 = k ∧ (planarRAMRun p ⟨207, M, R⟩ τ).natMem 28 = (16 * (n * n) + 16 * n + 48) ∧
      (planarRAMRun p ⟨207, M, R⟩ τ).natMem 40 = n ∧ (planarRAMRun p ⟨207, M, R⟩ τ).natMem 42 = (16 * (n * n) + 16 * n + 48) ∧
      (∀ a, a % 2 = 0 → 44 ≤ a → (planarRAMRun p ⟨207, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a % 2 = 0 → a ≠ 0 → (planarRAMRun p ⟨207, M, R⟩ τ).realMem a = R a) := by sorry
