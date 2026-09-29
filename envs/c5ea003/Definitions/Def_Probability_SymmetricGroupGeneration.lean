-- Prove2me | Definitions.Def_Probability_SymmetricGroupGeneration
-- name    : Probability_SymmetricGroupGeneration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:44.055998+00:00
-- url     : https://prove2.me/theorems/a0f93a73-f4c0-4231-9588-70d9a57178fc
-- title:
--   Aether Catalog definitions — Probability_SymmetricGroupGeneration
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SymmetricGroupGeneration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SymmetricGroupGeneration.lean by skeleton subtraction
import Mathlib
import Aesop
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-
Copyright (c) 2024 Harmonic Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The index-two obstruction to generating a finite group by two elements

For a finite group `G`, a natural probabilistic question (going back to work of
Netto, and made precise asymptotically by **Dixon's theorem** for the symmetric and
alternating groups) asks: if we pick two elements `a, b ∈ G` uniformly at random,
how likely is it that `⟨a, b⟩ = G`?

Dixon's theorem is an *asymptotic lower bound*: for `G = Sₙ` (or `Aₙ`) the
probability tends to `1` as `n → ∞`. That deep result is **not** the subject of this
file and is referenced here only as informal motivation.

This file isolates the elementary, exact **upper** obstruction that sits behind the
"`3/4` ceiling". The mechanism is purely group-theoretic:

* If `H ≤ G` is a *proper* subgroup and both chosen elements happen to lie in `H`,
  then the subgroup they generate is contained in `H`, hence is not all of `G`.
  Such pairs can never be generating pairs.
* When `H` has **index two** (`|G| = 2·|H|`), the count of these "both-in-`H`" pairs
  is `|H|² = |G|²/4`, so at least a quarter of all ordered pairs fail to generate.
  Consequently at most `3/4` of all ordered pairs can generate `G`.

The canonical index-two subgroup of `G = Sₙ` is the alternating group `Aₙ`
(the parity / sign obstruction): a pair of *even* permutations generates only even
permutations and so cannot generate `Sₙ`.

## Main results

* `bothInPairs_card`: the number of ordered pairs with both coordinates in `H` is
  `Fintype.card H ^ 2`.
* `genPairs_disjoint_bothInPairs`: for a proper `H`, no "both-in-`H`" pair is a
  generating pair (uses `Subgroup.closure_le`).
* `card_genPairs_le_compl_bothInPairs`: hence at most `|G|² - |H|²` generating pairs.
* `card_genPairs_le_three_quarters_of_card_eq_two_mul`: the clean arithmetic
  statement `4 · #genPairs ≤ 3 · |G|²` for an index-two subgroup `H`.
* `genProb_le_three_quarters`: the rational reformulation `genProb G ≤ 3/4`.
* `card_genPairs_perm_le_three_quarters`: the symmetric-group specialization using
  `H = alternatingGroup α`.

This `3/4` is an *upper* ceiling only; it says nothing about Dixon's asymptotic
*lower* bound, which requires entirely different (and far deeper) machinery.
-/

open scoped Classical

namespace SymmetricGroupGeneration

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The set of ordered pairs `(a, b)` that generate the whole group `G`. -/
noncomputable def genPairs (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Finset (G × G) :=
  Finset.univ.filter fun p : G × G => Subgroup.closure ({p.1, p.2} : Set G) = ⊤

/-- The set of ordered pairs `(a, b)` with both coordinates inside a subgroup `H`.
These are the "parity-obstruction" pairs: when `H` is proper they can never
generate `G`. -/
noncomputable def bothInPairs (H : Subgroup G) : Finset (G × G) :=
  Finset.univ.filter fun p : G × G => p.1 ∈ H ∧ p.2 ∈ H





/-- The probability that a uniformly random ordered pair generates `G`. -/
noncomputable def genProb (G : Type*) [Group G] [Fintype G] [DecidableEq G] : ℚ :=
  ((genPairs G).card : ℚ) / (Fintype.card G : ℚ) ^ 2


/-!
### Specialization to the symmetric group

For `G = Equiv.Perm α` the canonical index-two subgroup is `alternatingGroup α`,
the kernel of the sign homomorphism. Mathlib provides:

* `alternatingGroup.index_eq_two` : the alternating group has index `2`
  (for `Nontrivial α`), which forces it to be a *proper* subgroup; and
* `two_mul_card_alternatingGroup` : `2 * card (alternatingGroup α) = card (Perm α)`,
  i.e. `|Sₙ| = 2 · |Aₙ|`.

These are exactly the two inputs to the general index-two ceiling, so the `3/4`
upper bound transfers to `Sₙ` with no extra work. The hypothesis `2 ≤ card α`
is needed precisely to make `α` nontrivial; without it `alternatingGroup α = ⊤`
(the symmetric group on `0` or `1` points is trivial) and the bound is false.
-/


end SymmetricGroupGeneration


