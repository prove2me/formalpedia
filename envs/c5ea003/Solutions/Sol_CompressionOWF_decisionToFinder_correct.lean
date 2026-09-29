-- Prove2me | solution 1 for CompressionOWF.decisionToFinder_correct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:13:11.350957+00:00
-- url     : https://prove2.me/submissions/146ea44a-3e1a-4bb3-a0b1-14c42bc2ca6f

-- Sol generated from Speculative/AutoResearch/CompressionSearchToDecision.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionSearchToDecision
import Definitions.Def_Speculative_AutoResearch_CompressionUniversality
import Theorems.Thm_CompressionOWF_K_le_of_eq
import Theorems.Thm_CompressionOWF_exists_shortest
import Theorems.Thm_CompressionOWF_leastFrom_spec
import Theorems.Thm_CompressionOWF_rebuild_correct
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
theorem solution(D : Str → Str) (dec : Str → Str → ℕ → Bool)
    (fuel : ℕ → ℕ)
    (hdec : ∀ y w n, dec y w n = true ↔ ∃ p : Str, p.length = n ∧ D (w ++ p) = y)
    (y : Str) (hy : Describable D y) (hfuel : K D y ≤ fuel y.length) :
    D (decisionToFinder dec fuel y) = y ∧
      (decisionToFinder dec fuel y).length = K D y := by
  set P : ℕ → Bool := fun n => dec y [] n with hP
  have hPiff : ∀ n, P n = true ↔ ∃ p : Str, p.length = n ∧ D p = y := by
    intro n
    constructor
    · intro h
      obtain ⟨p, hp, hpy⟩ := (hdec y [] n).1 h
      exact ⟨p, hp, by simpa using hpy⟩
    · rintro ⟨p, hp, hpy⟩
      exact (hdec y [] n).2 ⟨p, hp, by simpa using hpy⟩
  obtain ⟨pK, hpKlen, hpKy⟩ := exists_shortest hy
  have hPK : P (K D y) = true := (hPiff _).2 ⟨pK, hpKlen, hpKy⟩
  have hex : ∃ n ≤ fuel y.length, P n = true := ⟨K D y, hfuel, hPK⟩
  obtain ⟨hgot, hmin⟩ := leastFrom_spec P (fuel y.length) hex
  set n0 := leastFrom P (fuel y.length) with hn0
  have hn0le : n0 ≤ K D y := by
    by_contra hcon
    push_neg at hcon
    have := hmin (K D y) hcon
    rw [hPK] at this
    exact absurd this (by simp)
  have hKle : K D y ≤ n0 := by
    obtain ⟨p, hp, hpy⟩ := (hPiff n0).1 hgot
    have := K_le_of_eq hpy
    omega
  have hn0eq : n0 = K D y := le_antisymm hn0le hKle
  obtain ⟨p, hp, hpy⟩ := (hPiff n0).1 hgot
  have hres : decisionToFinder dec fuel y = rebuild (dec y) n0 [] := rfl
  obtain ⟨h1, h2⟩ :=
    rebuild_correct D y (dec y) (fun w n => hdec y w n) n0 [] ⟨p, hp, by simpa using hpy⟩
  rw [hres]
  refine ⟨h1, ?_⟩
  rw [h2]
  simp [hn0eq]
