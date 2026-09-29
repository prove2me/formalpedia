-- Prove2me | solution 1 for Cryptography.BerggrenModular.Dive.card_multiples
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:03:47.378604+00:00
-- url     : https://prove2.me/submissions/4bcfd400-73d9-4a8b-83bf-04a88f0c7a0a

-- Sol generated from Cryptography/BerggrenModular/TrialDivisionEquivalence.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_BlumImmunity
import Definitions.Def_Cryptography_BerggrenModular_TrialDivisionEquivalence

/-!
# Trial-division equivalence and the guidance null for gcd dives

Experiment 555 measures the modular Berggren descent as a factoring device: a
"dive" walks nodes of the mod-`N` tree and tests `gcd(value, N)`.  The measured
exponent is `α = 1.007 ± 0.088` — the work to split `N` scales like the *smallest
prime factor*, i.e. trial division, and not like `√p_min` (Pollard ρ).  Two
further findings are (i) the various guidance heuristics gave no honest
improvement, and (ii) the naive `z = 12–24` "improvements" were pure
traversal-shape artefacts.

This file proves the exact combinatorial theorems behind those three statements
for the *ambient* model — a gcd dive that inspects `t` residues modulo `N` — and
then couples them back to the Berggren tree through
`Cryptography.BerggrenModular.BlumImmunity`.

## Main results

* `card_revealSet_semiprime` — modulo `N = p·q` exactly `p + q − 2` residues have
  a nontrivial gcd with `N`: the per-node hit rate is `(p+q−2)/pq ≍ 1/p_min`.
* `card_hitSet` — an **exact** formula for the number of `t`-node dives that
  succeed while inspecting the index set `S`.
* `hitSet_card_eq_of_card_eq` — **the guidance null.**  The success count depends
  on the inspection schedule `S` *only through its cardinality*: no ordering, no
  selection rule, no traversal shape changes it by a single dive.  Any measured
  "improvement" at fixed node budget is an artefact.
* `hitSet_card_eq_scaled` — the sharp form: examining `s` of `t` nodes has exactly
  the success rate of examining the first `s`.
* `hitSet_card_le_union_bound` — the union bound `#hits ≤ s·(p+q−2)·N^{t−1}`.
* `trial_division_scaling` — **α = 1.**  If the dive inspects fewer than `p/4`
  nodes its success probability is below `1/2`; equivalently
  `needs_linear_in_min_prime`: constant success needs `Ω(p_min)` nodes.  A ρ-like
  `O(√p_min)` dive is therefore impossible in this model.
* `card_reachableReveal` and `berggren_undersampling_ratio` — the Berggren
  hypotenuse stream can reach only `p − 1` of the `p + q − 2` revealing residues
  when `p ≡ 3 (mod 4)`: a strict, quantified under-sampling.
-/

open Cryptography
open BerggrenModular
open Dive

/-! ## The revealing residues -/










/-- A concrete instance of the count: modulo `15` the revealing residues are
`{3,5,6,9,10,12}`, six of them, and `3 + 5 - 2 = 6`. -/
example : revealSet 15 = {3, 5, 6, 9, 10, 12} := by decide

/-! ## Dives: sampling `t` nodes and inspecting a schedule `S` -/









/-! ## The guidance null -/




/-! ## Trial-division scaling: `α = 1` -/





/-! ## Coupling back to the Berggren tree: strict under-sampling -/






open Cryptography.BerggrenModular.Dive in
theorem solution(p q : ℕ) (hq : 0 < q) :
    ((Finset.range (p * q)).filter (fun x => q ∣ x)).card = p := by
  have h : (Finset.range (p * q)).filter (fun x => q ∣ x)
      = (Finset.range p).image (fun i => q * i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx, c, rfl⟩
      exact ⟨c, by rw [mul_comm p q] at hx; exact lt_of_mul_lt_mul_left hx (Nat.zero_le q), rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by rw [mul_comm p q]; exact (Nat.mul_lt_mul_left hq).2 hi, ⟨i, rfl⟩⟩
  rw [h, Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left hq hab),
    Finset.card_range]
