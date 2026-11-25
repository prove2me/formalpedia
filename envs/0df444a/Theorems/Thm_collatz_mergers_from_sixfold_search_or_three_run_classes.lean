-- Prove2me | Theorems.Thm_collatz_mergers_from_sixfold_search_or_three_run_classes
-- name    : collatz_mergers_from_sixfold_search_or_three_run_classes
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:55:08.66404+00:00
-- url     : https://prove2.me/theorems/c1d359ef-6a6e-5ba4-b1e1-bf909d5cfa9f
-- title:
--   Smaller Collatz mergers from the sixfold reverse search and three congruence classes
-- statement:
--   Let $C$ be the ordinary Collatz map. For a start $n$, use the following finite reverse test. Start at $lfloor(32n+1)/9
--   floor$ and make exactly $6n+1$ updates.
--
--   - Zero and every value outside the positive range below $6n+2$ are sent to zero.
--   - A positive value below $n$ stays fixed.
--   - For a remaining value $v$, take $(2v-1)/3$ if $vequiv2pmod3$.
--   - Otherwise, take $(4v-1)/3$ if $vequiv1pmod3$ and $2v<6n+2$. In every other case, send $v$ to zero.
--
--   Call the test successful if $nequiv7pmod9$ and its final state is positive and below $n$. Consider also the congruence classes
--   $$
--   nequiv444pmod{2187},qquad nequiv4408pmod{6561},qquad nequiv3229pmod{19683}.
--   $$
--
--   Suppose $nequiv15pmod{16}$ and either the reverse test succeeds or $n$ is in any of the three displayed congruence classes. Prove that a smaller positive start shares an ordinary iterate with $n$.
--
--   The requested merger is
--   $$
--   exists k,a,binmathbb N,qquad 0<k<n,qquad C^a(n)=C^b(k).
--   $$
-- source:
--   Sublemma of https://prove2.me/theorems/b7ac112c-5a9d-5208-a0ec-fa2cf7531dbc. The sixfold ancestor relay follows https://rstation.ai/problems/collatz/papers/213, Section 4.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

theorem collatz_mergers_from_sixfold_search_or_three_run_classes (n : ℕ) (hclass : n%16=15)
    (h : (n%9=7 ∧
      let next : ℕ → ℕ := fun v =>
        if 0<v ∧ v<6*n+2 then
          if v<n then v
          else if v%3=2 then (2*v-1)/3
          else if v%3=1 ∧ 2*v<6*n+2 then (4*v-1)/3
          else 0
        else 0
      let u := next^[6*n+1] ((32*n+1)/9)
      0<u ∧ u<n) ∨ n%2187=444 ∨ n%6561=4408 ∨ n%19683=3229) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  sorry
