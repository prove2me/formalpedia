-- Prove2me | solution 1 for ImmuneSystem.PAst.bounded_immunity_memory_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:21:50.760828+00:00
-- url     : https://prove2.me/submissions/1752fd01-5d63-4572-98f3-c30e225857b5

-- Sol generated from Shared/ImmuneBounded.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneBounded
import Definitions.Def_Shared_ImmuneEnsemble
import Definitions.Def_Shared_ImmuneQuarantine
import Definitions.Def_Shared_ImmuneSemantics
import Theorems.Thm_ImmuneSystem_PAst_attestation_memory_lower_bound
import Theorems.Thm_ImmuneSystem_PAst_effect_pad
import Theorems.Thm_ImmuneSystem_PAst_mem_astUniverse
import Theorems.Thm_ImmuneSystem_PAst_size_pad

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


@[simp] theorem litsBelow_lit (L n : ℕ) : litsBelow L (lit n) = decide (n < L) := rfl
@[simp] theorem litsBelow_ite (L : ℕ) (c a b : PAst) :
    litsBelow L (ite c a b) = (litsBelow L c && litsBelow L a && litsBelow L b) := rfl

/-- All padded variants have literals `< 2`. -/
theorem litsBelow_pad {L : ℕ} (hL : 2 ≤ L) (l : List Bool) : litsBelow L (pad l) = true := by
  induction l with
  | nil => simp [pad]; omega
  | cons b bs ih =>
      cases b <;> simp [pad, ih] <;> omega




open ImmuneSystem.PAst in
theorem solution{N L n : ℕ} (hL : 2 ≤ L) (hN : 3 * n + 1 ≤ N) :
    2 ^ n ≤ (boundedWhitelist N L).card := by
  refine attestation_memory_lower_bound (S := boundedWhitelist N L) (n := n) ?_
  intro t ht
  unfold padFamily at ht
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
  obtain ⟨v, rfl⟩ := ht
  refine mem_boundedWhitelist.2 ⟨?_, litsBelow_pad hL _, ?_⟩
  · rw [size_pad]
    simp only [List.length_ofFn]
    omega
  · unfold run
    exact effect_pad _ _
