-- Prove2me | solution 1 for twin_prime_conjecture_of_target
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-18T12:25:05.564975+00:00
-- url     : https://prove2.me/submissions/69d9f5ae-68d4-49f3-9586-3c61a83ac11c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Bounds.Basic
import Definitions.Def_a166944_record_core
import Theorems.Thm_A166944Research_unbounded_greater_twin_primes_of_target
import Theorems.Thm_A166944Research_a166944_record_is_greater_twin_prime

/-!
Reduction of `twin_prime_conjecture_of_target` to two lemmas.

`twin_prime_conjecture_of_target` takes `hTarget : Target` and concludes that the
set of twin-prime lower members is infinite. `Target` is exactly the statement
that every difference record above 5 is a greater twin prime, which is the child
theorem `a166944_record_is_greater_twin_prime`; so `hTarget` *is* that child,
applied. The remaining work is the standard infinitude argument, using the
already-proved child `unbounded_greater_twin_primes_of_target`.

The statement is not the conjecture: it shows the conjecture follows from the
record theorem. The child is Open, so this is a reduction.
-/

open A166944Research

theorem solution (hTarget : A166944Research.Target) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  have hrec : ∀ R : ℕ, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R :=
    fun R hR hd => hTarget R hR hd
  have hchild := a166944_record_is_greater_twin_prime
  -- above any bound there is a twin pair; take its lower member
  have hex : ∀ M : ℕ, ∃ q : ℕ, M < q ∧ Nat.Prime q ∧ Nat.Prime (q + 2) := by
    intro M
    obtain ⟨R, hMR, htwin⟩ :=
      unbounded_greater_twin_primes_of_target hTarget (max M 5 + 2)
    have hR2 : 2 ≤ R := by omega
    refine ⟨R - 2, by omega, htwin.2, ?_⟩
    rw [Nat.sub_add_cancel hR2]
    exact htwin.1
  classical
  choose g hg using hex
  have hg' : ∀ n : ℕ, n < g n ∧ Nat.Prime (g n) ∧ Nat.Prime (g n + 2) := hg
  -- iterating g from any starting point gives a strictly increasing sequence
  let F : ℕ → ℕ := fun n => Nat.recOn n (g 0) (fun k acc => g acc)
  have hFstep : ∀ n : ℕ, F n < F (n + 1) := by
    intro n
    have : F (n + 1) = g (F n) := rfl
    rw [this]
    exact (hg' (F n)).1
  have hFprime : ∀ n : ℕ, Nat.Prime (F n) ∧ Nat.Prime (F n + 2) := by
    intro n
    cases n with
    | zero => exact ⟨(hg' 0).2.1, (hg' 0).2.2⟩
    | succ n =>
        have : F (n + 1) = g (F n) := rfl
        rw [this]
        exact ⟨(hg' (F n)).2.1, (hg' (F n)).2.2⟩
  have hmono : StrictMono F := strictMono_nat_of_lt_succ hFstep
  have hrange : (Set.range F).Infinite := Set.infinite_range_of_injective hmono.injective
  refine hrange.mono ?_
  rintro p ⟨n, rfl⟩
  exact hFprime n
