-- Prove2me | solution 1 for EnergyAscent.descend_Bapply
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:00.52005+00:00
-- url     : https://prove2.me/submissions/614f51cf-9545-4089-ad48-99b0011ce756

-- Sol generated from Combinatorics/EnergyAscentWordDecoding.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentWordDecoding
import Theorems.Thm_EnergyAscent_hyp_lt_sum
import Theorems.Thm_EnergyAscent_invB1_B1
import Theorems.Thm_EnergyAscent_invB2_B2
import Theorems.Thm_EnergyAscent_invB3_B3
import Theorems.Thm_EnergyAscent_leg_lt_hyp

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














open EnergyAscent in
theorem solution{T : ℤ × ℤ × ℤ} (hT : Good T) (i : Fin 3) :
    descend (Bapply i T) = T := by
  obtain ⟨ha, hb, hc, hpt⟩ := hT
  have hlt := hyp_lt_sum ha hb hc hpt
  have hac : T.1 < T.2.2 := leg_lt_hyp hb hc hpt
  have hbc : T.2.1 < T.2.2 := by unfold IsPT at hpt; nlinarith
  fin_cases i
  · simp only [descend, Bapply, B1]
    rw [if_pos (show 4 * (T.1 - 2 * T.2.1 + 2 * T.2.2) <
      3 * (2 * T.1 - T.2.1 + 2 * T.2.2) by omega)]
    simpa [B1] using invB1_B1 T.1 T.2.1 T.2.2
  · simp only [descend, Bapply, B2]
    rw [if_neg (show ¬ (4 * (T.1 + 2 * T.2.1 + 2 * T.2.2) <
        3 * (2 * T.1 + T.2.1 + 2 * T.2.2)) by omega),
      if_neg (show ¬ (4 * (2 * T.1 + T.2.1 + 2 * T.2.2) <
        3 * (T.1 + 2 * T.2.1 + 2 * T.2.2)) by omega)]
    simpa [B2] using invB2_B2 T.1 T.2.1 T.2.2
  · simp only [descend, Bapply, B3]
    rw [if_neg (show ¬ (4 * (-T.1 + 2 * T.2.1 + 2 * T.2.2) <
        3 * (-2 * T.1 + T.2.1 + 2 * T.2.2)) by omega),
      if_pos (show 4 * (-2 * T.1 + T.2.1 + 2 * T.2.2) <
        3 * (-T.1 + 2 * T.2.1 + 2 * T.2.2) by omega)]
    simpa [B3] using invB3_B3 T.1 T.2.1 T.2.2
