-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_union_instance_build
-- name    : WilliamsonShmoys.ram_union_instance_build
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T07:11:31.960618+00:00
-- url     : https://prove2.me/theorems/ad593db9-0042-4275-a176-d67b1478e5b1
-- title:
--   RAM construction of the disjoint-union solver input in the odd sandbox cells
-- statement:
--   This RAM program writes the input of the single solver call in Baker's shifting technique into the odd memory cells. That input is the disjoint union of the $k$ masked graphs, one copy per shift class $c<k$.
--
--   Let a program $p$ contain, at position $b$, the 54-instruction program. Its working registers are the even cells $0,\dots,30$. On entry the memory holds $n$ in cell 32 and $k\ge1$ in cell 34. It also holds the original edge bits $E(v,w)$ at $36+2vn+2w$, the residues $m(v)=\mathrm{bakerLevel}(v)\bmod k$ at $\mathrm{LVB}+2v$ (an even $\mathrm{LVB}\ge36+2n^2$, in cell 28), and the real weights at the even real cells $32+2v$. Put $N=kn$ and number the vertices of the union as $a=cn+v$ for copy $c$ and vertex $v$. The program reaches $b+54$ within $((11n+20)n+12)k+20$ operations. It writes cell 1 $:=N$, cell 3 $:=3k$, and for all $c<k$ and $v,w<n$
--
--   $$\mathrm{nat}\bigl(5+2((cn+v)N+(cn+w))\bigr)=\begin{cases}1,& m(v)\ne c,\ m(w)\ne c,\ E(v,w)\ge1,\\ \text{unchanged},&\text{otherwise,}\end{cases}$$
--
--   $$\mathrm{real}\bigl(2(cn+v)+1\bigr)=\begin{cases}\mathrm{real}(32+2v),& m(v)\ne c,\\ \text{unchanged},&\text{otherwise.}\end{cases}$$
--
--   All even cells $\ge32$ are unchanged. All other odd natural cells, and all real cells other than $0$ and the written ones, are unchanged as well. In the odd-cell sandbox the subprogram's cell $x$ is the host's cell $2x+1$. If the odd cells were cleared beforehand (`ram_zero_odd_cells`), the odd cells then hold exactly `planarRAMInput N (3k) edge' weight'` for the disjoint union of the masked copies: cell $2+aN+a'$ becomes host cell $5+2(aN+a')$.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`. Positions are written as $5+2((c n+v)(k n)+(c n+w))$.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (shifting: one call on the union of the masked graphs)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_union_instance_build (p : List PlanarRAMInstruction) (b : ℕ)
    (hcode : CodeAt p b
    [natConst 0 0,
      natConst 2 1,
      natConst 4 2,
      natAdd 26 32 32,
      natAdd 30 28 26,
      natConst 8 0,
      natConst 6 0,
      natBranch 34 6 (b + 11) (b + 8),
      natAdd 8 8 32,
      natAdd 6 6 2,
      jump (b + 7),
      natAdd 10 8 8,
      natSub 24 10 26,
      natConst 10 1,
      natStore 10 8,
      natAdd 8 34 34,
      natAdd 8 8 34,
      natConst 10 3,
      natStore 10 8,
      natConst 6 0,
      natConst 18 5,
      natConst 22 1,
      natBranch 34 6 (b + 54) (b + 23),
      natAdd 12 28 0,
      natConst 20 32,
      natConst 16 36,
      natBranch 30 12 (b + 51) (b + 27),
      natLoad 8 12,
      natBranch 8 6 (b + 29) (b + 30),
      natBranch 6 8 (b + 44) (b + 30),
      realLoad 0 20,
      realStore 22 0,
      natAdd 14 28 0,
      natBranch 30 14 (b + 46) (b + 34),
      natLoad 10 14,
      natBranch 10 6 (b + 36) (b + 37),
      natBranch 6 10 (b + 40) (b + 37),
      natLoad 10 16,
      natBranch 2 10 (b + 39) (b + 40),
      natStore 18 2,
      natAdd 14 14 4,
      natAdd 16 16 4,
      natAdd 18 18 4,
      jump (b + 33),
      natAdd 16 16 26,
      natAdd 18 18 26,
      natAdd 18 18 24,
      natAdd 12 12 4,
      natAdd 20 20 4,
      natAdd 22 22 4,
      jump (b + 26),
      natAdd 18 18 26,
      natAdd 6 6 2,
      jump (b + 22)])
    (n k LVB : ℕ) (hk : 0 < k) (hLe : LVB % 2 = 0) (hL36 : 36 + 2 * n * n ≤ LVB)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = LVB) :
    ∃ τ, τ ≤ ((11 * n + 20) * n + 12) * k + 20 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).pc = b + 54 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 1 = k * n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 3 = 3 * k ∧
      (∀ c v w, c < k → v < n → w < n → (planarRAMRun p ⟨b, M, R⟩ τ).natMem (5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) =
        if M (LVB + 2 * v) ≠ c ∧ M (LVB + 2 * w) ≠ c ∧ 1 ≤ M (36 + 2 * v * n + 2 * w) then 1
        else M (5 + 2 * ((c * n + v) * (k * n) + (c * n + w)))) ∧
      (∀ c v, c < k → v < n → (planarRAMRun p ⟨b, M, R⟩ τ).realMem (2 * (c * n + v) + 1) =
        if M (LVB + 2 * v) ≠ c then R (32 + 2 * v) else R (2 * (c * n + v) + 1)) ∧
      (∀ a, a % 2 = 0 → 32 ≤ a → (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a % 2 = 1 → a ≠ 1 → a ≠ 3 → (∀ c v w, c < k → v < n → w < n → a ≠ 5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) →
        (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≠ 0 → (∀ c v, c < k → v < n → a ≠ 2 * (c * n + v) + 1) →
        (planarRAMRun p ⟨b, M, R⟩ τ).realMem a = R a) := by sorry
