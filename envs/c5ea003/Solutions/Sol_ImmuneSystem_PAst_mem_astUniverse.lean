-- Prove2me | solution 1 for ImmuneSystem.PAst.mem_astUniverse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:20:10.055823+00:00
-- url     : https://prove2.me/submissions/85ca527d-215d-4403-83d4-56172d7d2ce5

-- Sol generated from Shared/ImmuneBounded.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneBounded
import Definitions.Def_Shared_ImmuneEnsemble
import Theorems.Thm_ImmuneSystem_PAst_size_pos

/-!
# Algorithmic Immune System, Part VIII: bounded universes — perfect immunity and its price

Parts III, V and VII are impossibility results; Part IV gives containment at the
price of rigidity.  This part identifies the regime in which the algorithmic
immune system is *provably perfect*, and computes the price exactly.

Fix a size bound `N` and a literal bound `L`.  The programs of size `≤ N` whose
literals are `< L` form a finite universe (`mem_astUniverse`), so the monitor can
whitelist **all** benign programs of that universe:

* `bounded_perfect_immunity` — there is a whitelist `S` with
  * containment: every sanctioned program is harmless, hence by Part IV no
    adversary ever triggers the forbidden action, and
  * *zero false positives inside the universe*: every harmless program of the
    universe is accepted.
* `bounded_immunity_memory_lower_bound` — but any such whitelist has at least
  `2 ^ n` entries whenever `3n + 1 ≤ N` and `2 ≤ L`; i.e. its memory is
  exponential in the size bound, `2 ^ ((N-1)/3)`.

So perfect algorithmic immunity is attainable exactly on bounded code universes,
and the attestation database must then be exponentially large: the impossibility
results of Parts III/V/VII are the `N → ∞` limit of this trade-off.
-/

open ImmuneSystem
open PAst

open Finset














@[simp] theorem size_ite (c a b : PAst) :
    size (ite c a b) = 1 + size c + size a + size b := rfl
@[simp] theorem size_call (f a : PAst) : size (call f a) = 1 + size f + size a := rfl
@[simp] theorem litsBelow_lit (L n : ℕ) : litsBelow L (lit n) = decide (n < L) := rfl
@[simp] theorem litsBelow_ite (L : ℕ) (c a b : PAst) :
    litsBelow L (ite c a b) = (litsBelow L c && litsBelow L a && litsBelow L b) := rfl
@[simp] theorem litsBelow_call (L : ℕ) (f a : PAst) :
    litsBelow L (call f a) = (litsBelow L f && litsBelow L a) := rfl

open ImmuneSystem.PAst in
theorem solution(L : ℕ) :
    ∀ (n : ℕ) (t : PAst), size t ≤ n → litsBelow L t = true → t ∈ astUniverse n L := by
  intro n
  induction n with
  | zero =>
      intro t ht _
      exact absurd ht (by simpa using Nat.not_le.2 (size_pos t))
  | succ n ih =>
      intro t ht hl
      cases t with
      | inp => simp [astUniverse]
      | attack => simp [astUniverse]
      | lit m =>
          have hm : m < L := by simpa using hl
          simp only [astUniverse, Finset.mem_insert]
          refine Or.inr (Or.inr ?_)
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          exact Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, rfl⟩
      | ite c a b =>
          simp only [size_ite] at ht
          simp only [litsBelow_ite, Bool.and_eq_true] at hl
          obtain ⟨⟨hc, ha⟩, hb⟩ := hl
          have hcs : size c ≤ n := by omega
          have has : size a ≤ n := by omega
          have hbs : size b ≤ n := by omega
          simp only [astUniverse, Finset.mem_insert]
          refine Or.inr (Or.inr ?_)
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          refine Finset.mem_image.2 ⟨((c, a), b), ?_, rfl⟩
          simp only [Finset.mem_product]
          exact ⟨⟨ih c hcs hc, ih a has ha⟩, ih b hbs hb⟩
      | call f a =>
          simp only [size_call] at ht
          simp only [litsBelow_call, Bool.and_eq_true] at hl
          obtain ⟨hf, ha⟩ := hl
          have hfs : size f ≤ n := by omega
          have has : size a ≤ n := by omega
          simp only [astUniverse, Finset.mem_insert]
          refine Or.inr (Or.inr (Finset.mem_union_right _ ?_))
          refine Finset.mem_image.2 ⟨(f, a), ?_, rfl⟩
          simp only [Finset.mem_product]
          exact ⟨ih f hfs hf, ih a has ha⟩
