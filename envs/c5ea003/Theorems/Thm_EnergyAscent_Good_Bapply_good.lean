-- Prove2me | Theorems.Thm_EnergyAscent_Good_Bapply_good
-- name    : EnergyAscent.Good.Bapply_good
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:14:18.932368+00:00
-- url     : https://prove2.me/theorems/a34a01c6-461d-4e43-995d-1e8ac3e7c689
-- title:
--   Bapply good
-- statement:
--   Formal statement of `EnergyAscent.Good.Bapply_good` from the Aether Catalog (Combinatorics). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem EnergyAscent.Good.Bapply_good{T : ℤ × ℤ × ℤ} (hT : Good T) (i : Fin 3) :
--       Good (Bapply i T) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentWordDecoding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentWordDecoding.lean#L45

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

theorem EnergyAscent.Good.Bapply_good{T : ℤ × ℤ × ℤ} (hT : Good T) (i : Fin 3) :
    Good (Bapply i T) := by sorry
