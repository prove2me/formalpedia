-- Prove2me | solution 1 for Cryptography.BerggrenModular.Dive.miss_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:08:22.137453+00:00
-- url     : https://prove2.me/submissions/5be55375-46cf-4415-8409-9ca85139c5c3

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
theorem solution(N t : ℕ) (S : Finset (Fin t)) :
    (samples N t).filter (fun f => ¬ ∃ i ∈ S, Reveals N (f i))
      = Fintype.piFinset (fun j => if j ∈ S then avoidSet N else Finset.range N) := by
  ext f
  simp only [Finset.mem_filter, samples, Fintype.mem_piFinset, avoidSet, not_exists, not_and]
  constructor
  · rintro ⟨hmem, hno⟩ j
    by_cases hj : j ∈ S
    · simp only [hj, if_pos, Finset.mem_filter]
      exact ⟨hmem j, hno j hj⟩
    · simpa [hj] using hmem j
  · intro h
    refine ⟨fun j => ?_, fun i hi => ?_⟩
    · have hj := h j
      by_cases hjS : j ∈ S
      · simp only [hjS, if_pos, Finset.mem_filter] at hj; exact hj.1
      · simpa [hjS] using hj
    · have hi' := h i
      simp only [hi, if_pos, Finset.mem_filter] at hi'
      exact hi'.2
