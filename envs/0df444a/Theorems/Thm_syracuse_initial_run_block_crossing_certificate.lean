-- Prove2me | Theorems.Thm_syracuse_initial_run_block_crossing_certificate
-- name    : syracuse_initial_run_block_crossing_certificate
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T17:05:21.657047+00:00
-- url     : https://prove2.me/theorems/a82c640b-5eab-4f94-a322-faa9bb9d60b7
-- title:
--   Exact residue and crossing test for any two-halving block after the initial ascent
-- statement:
--   Set $n=2^kq-1$, $y=\operatorname{oddpart}(3^kq-1)$, $P=2^{s+1}4^d$, and $u=\lfloor(3^kq-1-2^s)/P\rfloor$. Suppose $s>0$ and $3^kq>1+2^s$. The exact initial endpoint relation $2^sy=3^kq-1$ together with $d$ steps of exactly two halvings is equivalent to the congruence $3^kq\equiv1+2^s\pmod P$. When this congruence holds, the entire block is determined. Each prefix at time $i\le d$ has value $1+2\cdot3^i4^{d-i}u$. The terminal value is below the original start exactly when $2+2\cdot3^d u<2^kq$. The block length and terminal exponent are arbitrary. There is no additional large-cofactor bound.
-- source:
--   Refines https://prove2.me/theorems/6cea8336-6355-4143-8aae-9d45bb0f0714 using syracuse_contraction_length_iff_dvd and https://prove2.me/theorems/401a4606-9af3-4b29-b0be-13ca8ceb3233.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_initial_run_block_crossing_certificate (k q s d : ℕ) (hs : 0 < s)
    (hgt : 1+2^s < 3^k*q) :
    let n := 2^k*q-1
    let y := ordCompl[2] (3^k*q-1)
    let p := 2^(s+1)*4^d
    let u := (3^k*q-(1+2^s))/p
    ((2^s*y = 3^k*q-1 ∧
      (∀ i : ℕ, i < d → 3*syracuseStep^[i] y+1 = 4*syracuseStep^[i+1] y)) ↔
        (3^k*q) % p = (1+2^s) % p) ∧
      ((3^k*q) % p = (1+2^s) % p →
        (∀ i : ℕ, i ≤ d → syracuseStep^[i] y = 1+2*(3^i*(4^(d-i)*u))) ∧
        (syracuseStep^[d] y < n ↔ 2+2*(3^d*u) < 2^k*q)) := by sorry
