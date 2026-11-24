-- Prove2me | Theorems.Thm_syracuse_next_step_descent_single_residue_after_initial_run
-- name    : syracuse_next_step_descent_single_residue_after_initial_run
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T12:10:14.284963+00:00
-- url     : https://prove2.me/theorems/76bf5987-7f91-4fce-b942-7e75d0d7de13
-- title:
--   One residue class for next-step descent after a surviving initial run
-- statement:
--   Write $n=2^kq-1$, $z=3^kq-1$, and $y=\operatorname{oddpart}(z)$. For $s>0$ with $2^{k+s}<3^k$, choose $b$ with $2^{k+s+b}\le3^{k+1}<2^{k+s+b+1}$, and put $P=2^{s+b+1}$. There is a single residue $r$ modulo $P$, specified by $3^{k+1}r+2^s\equiv3\pmod P$. For every $q\ge P+2^s+3$, membership in that residue class is equivalent to the conjunction $2^s y=z$, $n<y$, and $T(y)<n$. Thus it classifies all sufficiently large cofactors for this exact first-run valuation and next-step crossing. The prior initial-run formula makes $k+1$ the first strictly descending odd-step index in each such class.
-- source:
--   Refines https://prove2.me/theorems/747e0b8d-0cf3-4a0f-8330-b1f862f5898f using the exact dyadic test and the initial-run identity https://prove2.me/theorems/cd5cee3d-2614-45b1-abbd-326d3f73988d.

import Definitions.Def_syracuseStep
open Nat

theorem syracuse_next_step_descent_single_residue_after_initial_run (k s b : ℕ) (hs : 0 < s)
    (hup : 2^(k+s) < (3:ℕ)^k)
    (hlo : 2^(k+s+b) ≤ (3:ℕ)^(k+1))
    (hhi : (3:ℕ)^(k+1) < 2^(k+s+b+1)) :
    ∃ r < 2^(s+b+1),
      (∀ u : ℕ, (3^(k+1)*u+2^s) % 2^(s+b+1) = 3 % 2^(s+b+1) ↔
        u % 2^(s+b+1) = r) ∧ ∀ q : ℕ, 2^(s+b+1)+2^s+3 ≤ q →
      let z := 3^k*q-1
      let y := ordCompl[2] z
      (2^s*y=z ∧ 2^k*q-1 < y ∧ syracuseStep y < 2^k*q-1) ↔
        q % 2^(s+b+1) = r := by sorry
