-- Prove2me | solution 1 for LFunctionUniverse.periodicSeq_countable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:43:14.136527+00:00
-- url     : https://prove2.me/submissions/a13b7780-ae86-4553-85a7-8a7042e62e84

-- Sol generated from Applications/LFunctionUniverse/PeriodicUniverse.lean
import Mathlib
import Definitions.Def_Applications_LFunctionUniverse_PeriodicUniverse

/-!
# The L-function universe, part II: the periodic/arithmetic universe is countable

The Dirichlet L-functions — the L-functions attached to Dirichlet characters — have
coefficient sequences `a(k) = χ(k)` that are **periodic** (period dividing the
conductor) and take values in a **countable** set (roots of unity, together with
`0`).  This is the arithmetic constraint that tames the otherwise uncountable
universe of Dirichlet series studied in `NaiveUniverse.lean`.

The main abstract result of this file is:

* `periodicSeq_countable`: for any *countable* value type `V`, the set of periodic
  sequences `ℕ → V` is countable.

The intuition ("a periodic sequence is determined by a finite block of data") is
made precise via the surjection sending the finite data `(period, one full block of
values)` to the corresponding periodic sequence.

We then apply the countable-value idea to the genuine number-theoretic object: the
family of all Dirichlet characters (over all moduli) is countable, so there are only
countably many Dirichlet L-functions.
-/

open scoped Classical

open LFunctionUniverse











open LFunctionUniverse in
theorem solution{V : Type*} [Countable V] :
    {a : ℕ → V | IsPeriodicSeq a}.Countable := by
  -- the "finite data" `(period − 1, one block of values)` lives in a countable type
  let g : (Σ n : ℕ, Fin (n + 1) → V) → (ℕ → V) :=
    fun p k => p.2 ⟨k % (p.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hsub : {a : ℕ → V | IsPeriodicSeq a} ⊆ Set.range g := by
    rintro a ⟨n, hn, hper⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    refine ⟨⟨m, fun i => a i⟩, ?_⟩
    funext k
    simp only [g]
    rw [hper.map_mod_nat k]
  exact (Set.countable_range g).mono hsub
