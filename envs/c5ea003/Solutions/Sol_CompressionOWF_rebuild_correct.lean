-- Prove2me | solution 1 for CompressionOWF.rebuild_correct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:11:44.081583+00:00
-- url     : https://prove2.me/submissions/a2ee1669-2e52-4f15-9b49-58c442dc19c8

-- Sol generated from Speculative/AutoResearch/CompressionSearchToDecision.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionSearchToDecision
import Definitions.Def_Speculative_AutoResearch_CompressionUniversality
/-
Copyright (c) 2025. All rights reserved.

# Search-to-Decision for Compression, and its Cryptographic Payoff

## Overview

Third cycle of the Phase-B/M8 investigation (`Shared.CompressionOneWayFunctions`,
`Shared.CompressionUniversality`).

The previous cycles compared two *search* tasks — inverting a function and
finding shortest programs — and proved them equivalent.  The literature on
polynomial-time Kolmogorov complexity phrases hardness assumptions instead in
terms of the *decision* problem "is `K(y) ≤ n`?" (MINKT), so a complete
characterization must bridge search and decision.  That bridge is the classical
bit-by-bit prefix reconstruction, which we formalize here:

* `rebuild` — reconstruct a program one bit at a time from a *decision* oracle
  for the conditional predicate "some length-`n` continuation of the prefix `w`
  is a program for `y`";
* `rebuild_correct` — the reconstruction returns a genuine program of exactly the
  promised length (proved by induction on the number of remaining bits);
* `decisionToFinder_correct` — combining the reconstruction with the bounded
  search of `leastFrom` turns the decision oracle into a *shortest*-program
  finder;
* `decision_solves_inversion` — hence into an inverter;
* `owf_no_prefix_decider` — **cryptographic payoff**: if `f` is one-way for a
  class, then no algorithm of the class can decide the prefix-compressibility
  predicate of `f`.  The decision version of compression is hard exactly when
  one-way functions exist.

Together with cycle 1 (search version) and cycle 2 (approximate version), this
gives the promised map: *validity, exact-shortest, approximate-shortest and
prefix-decision compression tasks all sit at the same cryptographic level.*

No axioms beyond the standard three, no `sorry`.
-/

open CompressionOWF

/-! ## Section 1: Bit-by-bit reconstruction from a decision oracle -/



/-! ## Section 2: From the decision oracle to a shortest-program finder -/




/-! ## Section 3: Cryptographic payoff -/




open CompressionOWF in
theorem solution(D : Str → Str) (y : Str) (dec : Str → ℕ → Bool)
    (hdec : ∀ w n, dec w n = true ↔ ∃ p : Str, p.length = n ∧ D (w ++ p) = y) :
    ∀ (n : ℕ) (w : Str), (∃ p : Str, p.length = n ∧ D (w ++ p) = y) →
      D (rebuild dec n w) = y ∧ (rebuild dec n w).length = w.length + n := by
  intro n
  induction n with
  | zero =>
      intro w hw
      obtain ⟨p, hp, hpy⟩ := hw
      have hp0 : p = [] := List.eq_nil_of_length_eq_zero hp
      subst hp0
      simp only [rebuild, List.append_nil] at hpy ⊢
      exact ⟨hpy, by omega⟩
  | succ m ih =>
      intro w hw
      obtain ⟨p, hp, hpy⟩ := hw
      cases p with
      | nil => simp at hp
      | cons b t =>
          have htlen : t.length = m := by simpa using hp
          have hassoc : w ++ (b :: t) = (w ++ [b]) ++ t := by simp
          rw [hassoc] at hpy
          by_cases hbranch : dec (w ++ [false]) m = true
          · have hstep : rebuild dec (m + 1) w = rebuild dec m (w ++ [false]) := by
              simp [rebuild, hbranch]
            obtain ⟨q, hq, hqy⟩ := (hdec (w ++ [false]) m).1 hbranch
            obtain ⟨h1, h2⟩ := ih (w ++ [false]) ⟨q, hq, hqy⟩
            rw [hstep]
            refine ⟨h1, ?_⟩
            rw [h2]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          · -- the `false` branch is dead, so the surviving bit must be `true`
            have hbtrue : b = true := by
              cases b
              · exact absurd ((hdec (w ++ [false]) m).2 ⟨t, htlen, hpy⟩) hbranch
              · rfl
            subst hbtrue
            have hstep : rebuild dec (m + 1) w = rebuild dec m (w ++ [true]) := by
              simp [rebuild, hbranch]
            obtain ⟨h1, h2⟩ := ih (w ++ [true]) ⟨t, htlen, hpy⟩
            rw [hstep]
            refine ⟨h1, ?_⟩
            rw [h2]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
