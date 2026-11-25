-- Prove2me | Theorems.Thm_collatz_nondescending_merger_iff_sublevel_bridge
-- name    : collatz_nondescending_merger_iff_sublevel_bridge
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:36:06.826545+00:00
-- url     : https://prove2.me/theorems/c971d5b1-2681-520c-a817-eb3f835b7a4c
-- title:
--   A sublevel bridge characterizes smaller mergers of nondescending Collatz starts
-- statement:
--   Let $C$ be the ordinary Collatz map. Let $T$ be its shortcut map, so that an odd step is paired with the mandatory following halving. For a height $H$, write $asim_H b$ when $a$ and $b$ lie in the same component of the undirected graph of $T$ edges whose endpoints are below $H$.
--
--   Suppose $n$ is odd, $n
--   otequiv 2pmod 3$, and the entire ordinary orbit of $n$ stays at or above $n$. Prove that the following conditions are equivalent.
--
--   1. The ordinary orbit of $n$ meets the ordinary orbit of some $k$ with $0<k<n$.
--   2. There are $Hge 2n$ with $H>n$ and $Hequiv2pmod6$, and $0<k<n$, such that $n$ is unrelated to all smaller positive integers at height $H$. At the same height, one of the following holds, where $u=(2H-1)/3$ and $v=H/2$:
--      $$
--      (nsim_H u land vsim_H k)
--      quad	ext{or}quad
--      (nsim_H v land usim_H k).
--      $$
--
--   The second condition specifies the first possible height of a connection to a smaller component.
-- source:
--   Formalization of the sublevel-graph argument in Section 3 of https://rstation.ai/problems/collatz/papers/213, applied to https://prove2.me/theorems/db9b60ec-72e1-5e71-adc2-467b3036fcef.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

theorem collatz_nondescending_merger_iff_sublevel_bridge (n : ℕ)
    (hodd : n % 2 = 1) (hmod : n % 3 ≠ 2)
    (hstay : ∀ t : ℕ, n ≤ collatzStep^[t] n) :
    let shortcut : ℕ → ℕ := fun x =>
      if x % 2 = 0 then x / 2 else (3*x+1)/2
    let below : ℕ → ℕ → ℕ → Prop := fun H =>
      Relation.EqvGen (fun a b => a < H ∧ b < H ∧ shortcut a = b)
    (∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k) ↔
      ∃ H k : ℕ, n < H ∧ 2*n ≤ H ∧ 0 < k ∧ k < n ∧ H % 6 = 2 ∧
        (∀ j : ℕ, 0 < j → j < n → ¬ below H n j) ∧
        ((below H n ((2*H-1)/3) ∧ below H (H/2) k) ∨
          (below H n (H/2) ∧ below H ((2*H-1)/3) k)) := by
  sorry
