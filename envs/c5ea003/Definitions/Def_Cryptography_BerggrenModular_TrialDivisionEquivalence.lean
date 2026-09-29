-- Prove2me | Definitions.Def_Cryptography_BerggrenModular_TrialDivisionEquivalence
-- name    : Cryptography_BerggrenModular_TrialDivisionEquivalence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:10:31.474131+00:00
-- url     : https://prove2.me/theorems/708bde03-2be5-4c4c-9e09-81b86db2cb8f
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenModular_TrialDivisionEquivalence
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenModular.TrialDivisionEquivalence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenModular/TrialDivisionEquivalence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_BlumImmunity

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

namespace Cryptography
namespace BerggrenModular
namespace Dive

/-! ## The revealing residues -/

/-- A value `x` *reveals* a factor of `N` when `gcd x N` is a nontrivial divisor. -/
def Reveals (N x : ℕ) : Prop := 1 < Nat.gcd x N ∧ Nat.gcd x N < N

instance (N : ℕ) : DecidablePred (Reveals N) :=
  fun x => inferInstanceAs (Decidable (1 < Nat.gcd x N ∧ Nat.gcd x N < N))

/-- The residues below `N` that reveal a factor. -/
def revealSet (N : ℕ) : Finset ℕ := (Finset.range N).filter (Reveals N)

/-- The residues below `N` that reveal nothing. -/
def avoidSet (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun x => ¬ Reveals N x)






/-! ## Dives: sampling `t` nodes and inspecting a schedule `S` -/

/-- The space of `t`-node value streams modulo `N`. -/
def samples (N t : ℕ) : Finset (Fin t → ℕ) := Fintype.piFinset (fun _ => Finset.range N)


/-- The streams on which a dive that inspects the nodes indexed by `S` succeeds.
`S` models an arbitrary *guidance heuristic*: any rule that decides, in advance,
which of the `t` visited nodes to gcd-test, in any order. -/
def hitSet (N t : ℕ) (S : Finset (Fin t)) : Finset (Fin t → ℕ) :=
  (samples N t).filter (fun f => ∃ i ∈ S, Reveals N (f i))






/-! ## The guidance null -/




/-! ## Trial-division scaling: `α = 1` -/





/-! ## Coupling back to the Berggren tree: strict under-sampling -/





end Dive
end BerggrenModular


