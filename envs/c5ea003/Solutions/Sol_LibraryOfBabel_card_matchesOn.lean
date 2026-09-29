-- Prove2me | solution 1 for LibraryOfBabel.card_matchesOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:09:33.337538+00:00
-- url     : https://prove2.me/submissions/c19e8bd0-6454-4c7e-9e3b-9a00e938601c

-- Sol generated from Cryptography/LibraryOfBabel/Basic.lean
import Mathlib
import Definitions.Def_Cryptography_LibraryOfBabel_Basic
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
theorem solution{A L : ℕ} (S : Finset (Fin L)) (p : Fin L → Fin A) :
    Nat.card {s : Volume A L // MatchesOn S p s} = A ^ (L - S.card) := by
  classical
  let e : {s : Volume A L // MatchesOn S p s} ≃ ((↥(Sᶜ)) → Fin A) :=
  { toFun := fun s i => s.1 i
    invFun := fun f => ⟨fun i => if h : i ∈ S then p i else f ⟨i, by simp [h]⟩, by
      intro i hi; simp [hi]⟩
    left_inv := by
      rintro ⟨s, hs⟩; ext i
      by_cases h : i ∈ S
      · simp [h, hs i h]
      · simp [h]
    right_inv := by
      intro f; ext i
      have : (i : Fin L) ∉ S := Finset.mem_compl.mp i.2
      simp [this] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun]
  simp [Fintype.card_coe]
