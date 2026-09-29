-- Prove2me | solution 1 for ImmuneSystem.PAst.bounded_perfect_immunity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:27:27.654691+00:00
-- url     : https://prove2.me/submissions/76b0beb0-b20b-4fc8-8dab-4e86712fa6b7

-- Sol generated from Shared/ImmuneBounded.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneBounded
import Definitions.Def_Shared_ImmuneEnsemble
import Definitions.Def_Shared_ImmuneQuarantine
import Definitions.Def_Shared_ImmuneSemantics
import Theorems.Thm_ImmuneSystem_PAst_mem_astUniverse
import Theorems.Thm_ImmuneSystem_PAst_neutralization

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








theorem mem_boundedWhitelist {N L : ℕ} {t : PAst} :
    t ∈ boundedWhitelist N L ↔ size t ≤ N ∧ litsBelow L t = true ∧ run t = false := by
  unfold boundedWhitelist
  constructor
  · intro h; exact (Finset.mem_filter.1 h).2
  · intro h
    exact Finset.mem_filter.2 ⟨mem_astUniverse L N t h.1 h.2.1, h⟩






@[simp] theorem size_lit (n : ℕ) : size (lit n) = 1 := rfl
@[simp] theorem litsBelow_lit (L n : ℕ) : litsBelow L (lit n) = decide (n < L) := rfl

open ImmuneSystem.PAst in
theorem solution{N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    lit 0 ∈ boundedWhitelist N L ∧
      (∀ t ∈ boundedWhitelist N L, ¬ malicious t) ∧
      (∀ t : PAst, size t ≤ N → litsBelow L t = true → ¬ malicious t →
        t ∈ boundedWhitelist N L) ∧
      (∀ (adv : ℕ → PAst → PAst) (k : ℕ),
        ¬ malicious (trace (boundedWhitelist N L) (lit 0) adv k)) := by
  have hbase : lit 0 ∈ boundedWhitelist N L := by
    refine mem_boundedWhitelist.2 ⟨by simpa using hN, by simpa using hL, rfl⟩
  have hsafe : ∀ t ∈ boundedWhitelist N L, ¬ malicious t := by
    intro t ht
    have := (mem_boundedWhitelist.1 ht).2.2
    unfold malicious
    simp [this]
  refine ⟨hbase, hsafe, ?_, ?_⟩
  · intro t hs hlit hmal
    refine mem_boundedWhitelist.2 ⟨hs, hlit, ?_⟩
    unfold malicious at hmal
    simpa using hmal
  · intro adv k
    exact neutralization hbase hsafe adv k
