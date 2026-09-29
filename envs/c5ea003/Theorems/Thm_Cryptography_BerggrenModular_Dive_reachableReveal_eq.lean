-- Prove2me | Theorems.Thm_Cryptography_BerggrenModular_Dive_reachableReveal_eq
-- name    : Cryptography.BerggrenModular.Dive.reachableReveal_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:37:38.897262+00:00
-- url     : https://prove2.me/theorems/0c6d7897-7772-49fc-9ad6-87bedd77a56d
-- title:
--   The revealing residues a `p`-blind stream can ever reach: those divisible by
-- statement:
--   The revealing residues a `p`-blind stream can ever reach: those divisible by
--   `q` but not by `p`.
--
--   ```lean
--   theorem Cryptography.BerggrenModular.Dive.reachableReveal_eq{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
--       (revealSet (p * q)).filter (fun x => ¬ p ∣ x)
--         = ((Finset.range (p * q)).filter (fun x => q ∣ x)).erase 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenModular/TrialDivisionEquivalence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenModular/TrialDivisionEquivalence.lean#L354

-- Thm stub generated from Cryptography/BerggrenModular/TrialDivisionEquivalence.lean
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

theorem Cryptography.BerggrenModular.Dive.reachableReveal_eq{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (revealSet (p * q)).filter (fun x => ¬ p ∣ x)
      = ((Finset.range (p * q)).filter (fun x => q ∣ x)).erase 0 := by sorry
