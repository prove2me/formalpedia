-- Prove2me | Definitions.Def_Cryptography_LibraryOfBabel_Basic
-- name    : Cryptography_LibraryOfBabel_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:19:23.769497+00:00
-- url     : https://prove2.me/theorems/dd4f5a14-7402-41e2-a074-95bd77b8a950
-- title:
--   Aether Catalog definitions — Cryptography_LibraryOfBabel_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LibraryOfBabel.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LibraryOfBabel/Basic.lean by skeleton subtraction
import Mathlib
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

namespace LibraryOfBabel

/-- A **volume** of the Library: a book of `L` symbols over an alphabet of size `A`. -/
abbrev Volume (A L : ℕ) : Type := Fin L → Fin A


/-- `MatchesOn S p s` says the volume `s` agrees with the prescribed text `p` on
every position in the finite set `S`. -/
def MatchesOn {A L : ℕ} (S : Finset (Fin L)) (p : Fin L → Fin A) (s : Volume A L) : Prop :=
  ∀ i ∈ S, s i = p i


/-- `OccursAt idx p s` says the volume `s` carries the length-`m` pattern `p` at
the positions listed by the family `idx : Fin m → Fin L`. -/
def OccursAt {A L m : ℕ} (idx : Fin m → Fin L) (p : Fin m → Fin A) (s : Volume A L) : Prop :=
  ∀ j, s (idx j) = p j


/-! Instances needed downstream. `Fin A` is nonempty exactly when `A > 0`. -/

/-- The Library is nonempty as soon as the alphabet is nonempty. -/
instance (A L : ℕ) [NeZero A] : Nonempty (Volume A L) := by
  refine ⟨fun _ => ?_⟩
  exact ⟨0, Nat.pos_of_ne_zero (NeZero.ne A)⟩

end LibraryOfBabel


