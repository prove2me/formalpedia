-- Prove2me | Definitions.Def_Algebra_NumberTheory_FibEntry
-- name    : Algebra_NumberTheory_FibEntry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:26:05.160402+00:00
-- url     : https://prove2.me/theorems/db92e5c2-0770-425e-8094-8f006fe2292e
-- title:
--   Aether Catalog definitions — Algebra_NumberTheory_FibEntry
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.NumberTheory.FibEntry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/NumberTheory/FibEntry.lean by skeleton subtraction
import Mathlib
/-
# Fibonacci Entry Point (Rank of Apparition)

This file establishes the basic theory of the Fibonacci entry point (rank of apparition):
for each prime p, the smallest positive index k such that p ∣ F_k.

Key results:
- `fib_entry_exists`: Every prime has an entry point
- `fib_dvd_iff_entry_dvd`: p ∣ F_n ↔ entry(p) ∣ n
-/

open Nat

set_option maxHeartbeats 800000

/-! ## Entry point existence -/

/-
Every prime divides some positive-index Fibonacci number.
This follows from the pigeonhole principle: the pairs (F_n mod p, F_{n+1} mod p)
must repeat among the first p² + 1 values, and the recurrence is invertible,
so F_0 = 0 recurs.
-/
lemma fib_entry_exists (p : ℕ) (hp : p.Prime) : ∃ k, 0 < k ∧ p ∣ Nat.fib k := by
  -- By the pigeonhole principle, since there are only $p^2$ possible pairs $(F_n \mod p, F_{n+1} \mod p)$, the sequence must eventually repeat.
  have h_pigeonhole : ∃ i j : ℕ, i < j ∧ (fib i % p = fib j % p) ∧ (fib (i + 1) % p = fib (j + 1) % p) := by
    have h_finite : Set.Finite (Set.range fun n => (fib n % p, fib (n + 1) % p)) := by
      exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ p - 1, p - 1 ⟩, by rintro a ⟨ n, rfl ⟩ ; exact ⟨ Nat.le_sub_one_of_lt ( Nat.mod_lt _ hp.pos ), Nat.le_sub_one_of_lt ( Nat.mod_lt _ hp.pos ) ⟩ ⟩;
    contrapose! h_finite;
    exact Set.infinite_range_of_injective fun i j hij => le_antisymm ( le_of_not_gt fun hi => h_finite _ _ hi ( by aesop ) ( by aesop ) ) ( le_of_not_gt fun hj => h_finite _ _ hj ( by aesop ) ( by aesop ) );
  obtain ⟨ i, j, hij, hi, hj ⟩ := h_pigeonhole; induction' i with i ih generalizing j; induction' j with j ihj; aesop; (
  exact ⟨ j + 1, Nat.succ_pos _, Nat.dvd_of_mod_eq_zero <| by simpa using hi.symm ⟩);
  specialize ih ( j - 1 ) ( Nat.lt_pred_iff.mpr hij ) ; rcases j <;> simp_all +arith +decide [ Nat.fib_add_two, Nat.add_mod ] ;
  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ]

/-! ## Entry point definition -/

/-- The entry point (rank of apparition) of a prime p in the Fibonacci sequence:
the smallest positive k such that p ∣ F_k. -/
noncomputable def fibEntryPoint (p : ℕ) (hp : p.Prime) : ℕ :=
  Nat.find (fib_entry_exists p hp)




/-! ## Entry point divides -/

/-
If p ∣ F_n with n > 0, then the entry point of p divides n.
Uses `Nat.fib_gcd`: gcd(F_m, F_n) = F_{gcd(m, n)}.
-/


