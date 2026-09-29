-- Prove2me | solution 1 for ThreeCubes.hasse_of_abs_le_113
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:58:30.960128+00:00
-- url     : https://prove2.me/submissions/4aa5749a-32dc-4c1e-860e-af9f54354545

-- Sol generated from Probability/Witnesses.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Witnesses
import Theorems.Thm_ThreeCubes_isSumOfThreeCubes_neg
import Theorems.Thm_ThreeCubes_isSumOfThreeCubes_of_nonneg_le_113
import Theorems.Thm_ThreeCubes_locallySolvable_iff

/-!
# Verified computational results and the Hasse principle for `x³ + y³ + z³ = n`

The theorem `ThreeCubes.locallySolvable_iff` shows that the only local obstruction is the
congruence mod `9`.  Whether every locally solvable `n` is *globally* solvable — the Hasse
principle for the affine surface — is a famous open problem.  Here we

* reformulate the conjecture purely in congruence terms (`hasse_iff_congruence`);
* **verify it for every `n` with `|n| ≤ 113`**, using explicit representations checked by the
  Lean kernel.  This is the widest window currently possible: `114` is the smallest positive
  integer that is locally solvable and for which no representation is known.  Several of the
  witnesses are genuinely large, the most famous being
  `33 = 8866128975287528³ - 8778405442862239³ - 2736111468807040³` and
  `42 = (-80538738812075974)³ + 80435758145817515³ + 12602123297335631³`;
* record a second, huge representation of `3`.
-/

open ThreeCubes







open ThreeCubes in
theorem solution(n : ℤ) (h : |n| ≤ 113) : HasseHolds n := by
  intro hL
  obtain ⟨h4, h5⟩ := (locallySolvable_iff n).mp hL
  rw [abs_le] at h
  obtain ⟨hlo, hhi⟩ := h
  by_cases hn : 0 ≤ n
  · exact isSumOfThreeCubes_of_nonneg_le_113 n hn hhi h4 h5
  · push_neg at hn
    have hneg := isSumOfThreeCubes_of_nonneg_le_113 (-n) (by omega) (by omega)
      (by omega) (by omega)
    simpa using isSumOfThreeCubes_neg hneg
