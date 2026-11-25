-- Prove2me | Theorems.Thm_collatz_coalescence_at_arbitrary_odd_run_exit
-- name    : collatz_coalescence_at_arbitrary_odd_run_exit
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:39:05.984802+00:00
-- url     : https://prove2.me/theorems/db365a45-6d10-4f2b-b676-ece416024892
-- title:
--   A smaller Collatz merger at an exit after arbitrarily many odd runs
-- statement:
--   Let $C$ be the ordinary Collatz map. For a positive integer $x$, put
--   $$
--   r=v_2(x+1),qquad E(x)=3^r(x+1)/2^r-1,qquad
--   J(x)=E(x)/2^{v_2(E(x))}.
--   $$
--
--   For $j,s,einmathbb N$, write $w=E(J^j(n))$. When $2^smid w$, define
--   $$
--   y=w/2^s,qquad z=2^e y+1,qquad u=v_3(z),qquad
--   k_e=2^u z/3^u-1 .
--   $$
--
--   If $n>0$ and some such triple has $y<n$ or $k_e<n$, prove that a smaller positive start meets the orbit of $n$.
--   $$
--   exists k,a,binmathbb N,qquad 0<k<n,qquad C^a(n)=C^b(k).
--   $$
--
--   The numbers of completed runs, terminal halvings, and halvings on the smaller-start path are unrestricted.
-- source:
--   Extension of the odd-run arithmetic in https://prove2.me/theorems/d4d84904-742f-506d-9aa7-c281ccc7403b for https://prove2.me/theorems/58921f6a-9304-4a57-82ac-207ec9bc4c3b.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_coalescence_at_arbitrary_odd_run_exit (n : ℕ) (hn : 0 < n)
    (h : let runEnd : ℕ → ℕ := fun x =>
        let r := (x+1).factorization 2
        3^r*((x+1)/2^r)-1
      let jump : ℕ → ℕ := fun x =>
        let w := runEnd x
        w/2^(w.factorization 2)
      ∃ j s e : ℕ,
        let w := runEnd (jump^[j] n)
        let y := w/2^s
        let z := 2^e*y+1
        let r := z.factorization 3
        2^s ∣ w ∧ (y < n ∨ 2^r*(z/3^r)-1 < n)) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by sorry
