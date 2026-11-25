-- Prove2me | Theorems.Thm_WilliamsonShmoys_union_input_decode
-- name    : WilliamsonShmoys.union_input_decode
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T10:54:29.750877+00:00
-- url     : https://prove2.me/theorems/c79076be-dad9-575c-b9e3-11e6862faf50
-- title:
--   Odd host cells hold the solver input of the union instance
-- statement:
--   This lemma identifies the memory prepared by the host with the standard input of the subroutine solver in the odd-cell sandbox.
--
--   Let $n\ge1$, $k$, and put $N=kn$. Number the union vertices $x<N$ as copy $x/n$ and vertex $x\bmod n$. Given residues $m(v)$, edge bits $E(v,w)$ and weights $\omega(v)$, define
--
--   $$\mathrm{edge}'(x,y)=\bigl[x/n=y/n,\ m(x\bmod n)\ne x/n,\ m(y\bmod n)\ne x/n,\ E(x\bmod n,y\bmod n)\ge1\bigr],$$
--
--   $$\omega'(x)=\begin{cases}\omega(x\bmod n),& m(x\bmod n)\ne x/n,\\ 0,&\text{otherwise.}\end{cases}$$
--
--   Suppose the host memory has cell 1 $=N$, cell 3 $=3k$, cell $5+2((cn+v)N+(cn+w))=[m(v)\ne c,\ m(w)\ne c,\ E(v,w)\ge1]$, and real cell $2(cn+v)+1=\omega'(cn+v)$ for $c<k$ and $v,w<n$, with all other odd natural and real cells zero. Then for every $a$,
--
--   $$\mathrm{nat}(2a+1)=\mathrm{input}(a),\qquad \mathrm{real}(2a+1)=\mathrm{input}_{\mathbb R}(a),$$
--
--   where input is `planarRAMInput N (3k) edge' ω'`. This is exactly the memory part of `SandboxOddRel` needed to start the sandboxed solver.
--
--   **Formalization Note.** `planarRAMInput` is from `Def_WilliamsonShmoys_PlanarIndependentSetRAM`. The conditions are the outputs of `ram_zero_odd_cells` and `ram_union_instance_build`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (subroutine call)

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM

set_option autoImplicit false
open WilliamsonShmoys
open Classical

theorem WilliamsonShmoys.union_input_decode (n k : ℕ) (hn : 0 < n) (mk : ℕ → ℕ) (eb : ℕ → ℕ → ℕ) (wt : ℕ → ℝ)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h1 : M 1 = k * n) (h3 : M 3 = 3 * k)
    (hT : ∀ c v w, c < k → v < n → w < n → M (5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) =
      if mk v ≠ c ∧ mk w ≠ c ∧ 1 ≤ eb v w then 1 else 0)
    (hO : ∀ a, a % 2 = 1 → a ≠ 1 → a ≠ 3 →
      (∀ c v w, c < k → v < n → w < n → a ≠ 5 + 2 * ((c * n + v) * (k * n) + (c * n + w))) → M a = 0)
    (hR : ∀ c v, c < k → v < n → R (2 * (c * n + v) + 1) = if mk v ≠ c then wt v else 0)
    (hRO : ∀ a, a % 2 = 1 → (∀ c v, c < k → v < n → a ≠ 2 * (c * n + v) + 1) → R a = 0) :
    (∀ a, M (2 * a + 1) = (planarRAMInput (k * n)
      (3 * k) (fun x y => decide (x.val / n = y.val / n ∧ mk (x.val % n) ≠ x.val / n ∧ mk (y.val % n) ≠ x.val / n ∧
        1 ≤ eb (x.val % n) (y.val % n)))
      (fun x => if mk (x.val % n) ≠ x.val / n then wt (x.val % n) else 0)).natMem a) ∧
    (∀ a, R (2 * a + 1) = (planarRAMInput (k * n)
      (3 * k) (fun x y => decide (x.val / n = y.val / n ∧ mk (x.val % n) ≠ x.val / n ∧ mk (y.val % n) ≠ x.val / n ∧
        1 ≤ eb (x.val % n) (y.val % n)))
      (fun x => if mk (x.val % n) ≠ x.val / n then wt (x.val % n) else 0)).realMem a) := by sorry
