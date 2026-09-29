-- Prove2me | solution 1 for EnergyAscent.Good.Bapply_good
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:14:18.294801+00:00
-- url     : https://prove2.me/submissions/b4852a81-6e8f-4582-9325-224a664ac26c

-- Sol generated from Combinatorics/EnergyAscentWordDecoding.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentWordDecoding
import Theorems.Thm_EnergyAscent_B1_isPT
import Theorems.Thm_EnergyAscent_B2_isPT
import Theorems.Thm_EnergyAscent_B3_isPT
import Theorems.Thm_EnergyAscent_hyp_lt_sum
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
    Good (Bapply i T) := by
  obtain ⟨ha, hb, hc, hpt⟩ := hT
  have hlt := hyp_lt_sum ha hb hc hpt
  have hac : T.1 < T.2.2 := leg_lt_hyp hb hc hpt
  have hbc : T.2.1 < T.2.2 := by unfold IsPT at hpt; nlinarith
  fin_cases i
  · exact ⟨by simp only [Bapply, B1]; omega, by simp only [Bapply, B1]; omega,
      by simp only [Bapply, B1]; omega, B1_isPT hpt⟩
  · exact ⟨by simp only [Bapply, B2]; omega, by simp only [Bapply, B2]; omega,
      by simp only [Bapply, B2]; omega, B2_isPT hpt⟩
  · exact ⟨by simp only [Bapply, B3]; omega, by simp only [Bapply, B3]; omega,
      by simp only [Bapply, B3]; omega, B3_isPT hpt⟩
