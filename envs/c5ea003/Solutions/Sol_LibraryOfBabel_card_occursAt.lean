-- Prove2me | solution 1 for LibraryOfBabel.card_occursAt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:11:31.053721+00:00
-- url     : https://prove2.me/submissions/e3a70aa9-80b3-40d8-accf-eb0b08fda2ab

-- Sol generated from Cryptography/LibraryOfBabel/Basic.lean
import Mathlib
import Definitions.Def_Cryptography_LibraryOfBabel_Basic
import Theorems.Thm_LibraryOfBabel_card_matchesOn
import Theorems.Thm_LibraryOfBabel_card_volume
/-
# The Library of Babel: Combinatorics of the Universal Library (Core)

Borges' *Library of Babel* is the set of **all** books of a fixed length over a
fixed alphabet.  We formalise a *volume* as a function `Fin L → Fin A` (a string
of `L` symbols drawn from an alphabet of size `A`), and the whole Library as the
finite type of all such volumes.

## Main Results (this file)

1. **Library size** (`card_volume`): the Library has exactly `A ^ L` volumes.
   For Borges' parameters `A = 25`, `L = 1312000` this is `25 ^ 1312000`.

2. **Constrained-content count** (`card_matchesOn`): the number of volumes whose
   content is prescribed on a set `S` of `S.card` positions is exactly
   `A ^ (L - S.card)` — fixing a symbol removes exactly one factor of `A`.

3. **Pattern-occurrence count** (`card_occursAt`): for an injective family of
   `m` positions, the number of volumes carrying a prescribed length-`m` pattern
   there is `A ^ (L - m)`.  This is the exact "how many books contain this exact
   passage at this exact place" count that underlies the probability estimates.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the size of the Library is `A^L`, and fixing the text
on `d` positions divides the population by `A^d`.  Both are combinatorial
counting facts, but they are the quantitative backbone of every "probability of
finding meaning" statement in the theme.

Experiment (Experimenter): computed small cases.  `A=4, L=2` gives `16` volumes;
fixing one position leaves `4 = 4^(2-1)`.  `A=2, L=3` gives `8`; a fixed length-2
window leaves `2 = 2^(3-2)`.  All match `A^(L-d)`.

Analysis (Analyst): the clean proof is the bijection
`{s // s = p on S} ≃ (Sᶜ → Fin A)` (restrict / glue), giving `A^(L - S.card)`.
The pattern version follows by taking `S` to be the (injective) image of the
window index family, whose cardinality is `m`.  We phrase the counts with
`Nat.card` (instance-independent) to avoid a `Fintype` instance diamond that
appears once the whole of Mathlib is in scope.
-/

open Finset Fintype Function

open LibraryOfBabel







/-! Instances needed downstream. `Fin A` is nonempty exactly when `A > 0`. -/



open LibraryOfBabel in
theorem solution{A L m : ℕ} (idx : Fin m → Fin L) (hidx : Function.Injective idx)
    (p : Fin m → Fin A) :
    Nat.card {s : Volume A L // OccursAt idx p s} = A ^ (L - m) := by
  classical
  -- The `m = 0` case: the pattern constraint is vacuous.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hall : ∀ s : Volume A L, OccursAt idx p s := by
      intro s j; exact absurd j.2 (by omega)
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), card_volume, Nat.sub_zero]
  -- The `m > 0` case: we have a fallback symbol `p ⟨0, hmpos⟩ : Fin A`.
  set S : Finset (Fin L) := Finset.univ.image idx with hS
  have hScard : S.card = m := by
    rw [hS, Finset.card_image_of_injective _ hidx]; simp
  -- The volumes carrying the pattern are exactly those matching a suitable `q` on `S`.
  let q : Fin L → Fin A := fun k =>
    if h : ∃ j, idx j = k then p (Classical.choose h) else p ⟨0, hmpos⟩
  have hqidx : ∀ j, q (idx j) = p j := by
    intro j
    have hex : ∃ j', idx j' = idx j := ⟨j, rfl⟩
    simp only [q, dif_pos hex]
    have := Classical.choose_spec hex
    exact congrArg p (hidx this)
  have hiff : ∀ s : Volume A L, OccursAt idx p s ↔ MatchesOn S q s := by
    intro s
    constructor
    · intro h k hk
      rw [hS, Finset.mem_image] at hk
      obtain ⟨j, _, rfl⟩ := hk
      rw [h j, hqidx j]
    · intro h j
      have hk : idx j ∈ S := by rw [hS, Finset.mem_image]; exact ⟨j, by simp⟩
      rw [h (idx j) hk, hqidx j]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), card_matchesOn, hScard]
