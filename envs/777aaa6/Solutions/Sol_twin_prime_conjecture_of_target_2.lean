-- Prove2me | solution 2 for twin_prime_conjecture_of_target
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-20T00:22:41.669003+00:00
-- url     : https://prove2.me/submissions/8fab1365-3b66-46f2-8b0a-fec41aef97b1

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Lattice
import Definitions.Def_a166944_record_core
import Theorems.Thm_A166944Research_unbounded_greater_twin_primes_of_target

open A166944Research

/-- A finite set of lower twins cannot accommodate the unbounded upper twins
supplied by the record conjecture.  The conjecture itself is an input. -/
theorem solution (hTarget : A166944Research.Target) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  intro hfin
  obtain ⟨b, hb⟩ := hfin.bddAbove
  obtain ⟨R, hR, hpair⟩ := unbounded_greater_twin_primes_of_target hTarget (b + 2)
  have hR2 : 2 ≤ R := by omega
  have hmem : R - 2 ∈ {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} := by
    exact ⟨hpair.2, (Nat.sub_add_cancel hR2).symm ▸ hpair.1⟩
  have hle : R - 2 ≤ b := hb hmem
  omega
