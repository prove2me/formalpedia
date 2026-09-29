-- Prove2me | Theorems.Thm_EnergyAscent_descend_Bapply
-- name    : EnergyAscent.descend_Bapply
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:16:42.841831+00:00
-- url     : https://prove2.me/theorems/45fcc3b8-280e-4994-af58-f3ce6c9b5aad
-- title:
--   The band-selected descent inverts the band-named generator: one step of the
-- statement:
--   The band-selected descent inverts the band-named generator: one step of the
--   decoder undoes one step of the tree.
--
--   ```lean
--   theorem EnergyAscent.descend_Bapply{T : ℤ × ℤ × ℤ} (hT : Good T) (i : Fin 3) :
--       descend (Bapply i T) = T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentWordDecoding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentWordDecoding.lean#L68

-- Thm stub generated from Combinatorics/EnergyAscentWordDecoding.lean
import Mathlib
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentWordDecoding

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

open EnergyAscent

theorem EnergyAscent.descend_Bapply{T : ℤ × ℤ × ℤ} (hT : Good T) (i : Fin 3) :
    descend (Bapply i T) = T := by sorry
