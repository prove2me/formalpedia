-- Prove2me | Definitions.Def_Combinatorics_EnergyAscentWordDecoding
-- name    : Combinatorics_EnergyAscentWordDecoding
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:42:19.807929+00:00
-- url     : https://prove2.me/theorems/52e0f1fd-0630-4e5c-8f9f-ffc5b12616ab
-- title:
--   Aether Catalog definitions — Combinatorics_EnergyAscentWordDecoding
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EnergyAscentWordDecoding`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EnergyAscentWordDecoding.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters

/-!
# Energy-Ascent VI: the whole branch word is positional

Energy-Ascent I proved that the *first* Berggren letter is exactly a leg-ratio
band.  The experimental round also measured a joint signal on `(b₁, b₂)`.  Here
we settle the general case: **the entire branch word of a Berggren triple is
decodable from ratio bands alone**, by iterating the band-selected descent.

The decoder `readWord` never inspects a residue, a factorisation, or the
hypotenuse's arithmetic — only three linear comparisons per step.  The main
theorem `EnergyAscent.readWord_applyWord` says it inverts the generator word
exactly, for every word and every admissible starting triple.

## Main results

* `EnergyAscent.descend`: the descent selected by the ratio band.
* `EnergyAscent.descend_Bapply`: the band-selected descent inverts the
  band-named generator.
* `EnergyAscent.readWord_applyWord`: reading `|w|` letters off
  `applyWord w T` returns `w`.
* `EnergyAscent.secondLetter_Bapply`: the specialisation to depth two, the
  formal counterpart of the measured joint `(b₁, b₂)` signal.
-/

namespace EnergyAscent

/-- A triple that is Pythagorean with strictly positive entries. -/
def Good (T : ℤ × ℤ × ℤ) : Prop :=
  0 < T.1 ∧ 0 < T.2.1 ∧ 0 < T.2.2 ∧ IsPT T.1 T.2.1 T.2.2

/-- The Barning–Hall generator named by a letter. -/
def Bapply : Fin 3 → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ
  | 0, T => B1 T.1 T.2.1 T.2.2
  | 1, T => B2 T.1 T.2.1 T.2.2
  | 2, T => B3 T.1 T.2.1 T.2.2

/-- The descent selected by the ratio band of the legs. -/
def descend (T : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if 4 * T.1 < 3 * T.2.1 then invB1 T.1 T.2.1 T.2.2
  else if 4 * T.2.1 < 3 * T.1 then invB3 T.1 T.2.1 T.2.2
  else invB2 T.1 T.2.1 T.2.2




/-- Apply a word of generators, leftmost letter last. -/
def applyWord : List (Fin 3) → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ
  | [], T => T
  | i :: w, T => Bapply i (applyWord w T)

/-- The positional decoder: read `n` letters by iterating the band-selected
descent. -/
def readWord : ℕ → ℤ × ℤ × ℤ → List (Fin 3)
  | 0, _ => []
  | n + 1, T => branchLetter T.1 T.2.1 :: readWord n (descend T)



/-- The second letter of a triple, read positionally. -/
def secondLetter (T : ℤ × ℤ × ℤ) : Fin 3 :=
  branchLetter (descend T).1 (descend T).2.1


end EnergyAscent


