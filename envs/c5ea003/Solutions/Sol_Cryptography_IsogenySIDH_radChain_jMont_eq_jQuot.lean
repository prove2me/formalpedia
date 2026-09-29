-- Prove2me | solution 1 for Cryptography.IsogenySIDH.radChain_jMont_eq_jQuot
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:45:52.568631+00:00
-- url     : https://prove2.me/submissions/3a096cca-56d8-4837-bed8-57a1d25b3a32

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
open Cryptography.IsogenySIDH in
theorem solution {K : Type*} [Field K] {r : ℕ → K} {A : K} (htwo : (2 : K) ≠ 0)
    (h : NonsingularWalk r A) (n : ℕ) :
    jMont (radChain r A (n + 1)) = jQuot (radChain r A n) := by
  obtain ⟨hα0, hα2⟩ := h.1 n
  have hsing := h.2 n
  have hrc : radChain r A (n + 1) = radTwoParam (radChain r A n) (r n) := rfl
  rw [hrc]
  unfold jMont jQuot radTwoParam
  set a := radChain r A n with ha
  set α := r n with hα
  have h4 : (4 : K) ≠ 0 := by
    have := mul_ne_zero htwo htwo
    norm_num at this
    exact this
  have ha2 : a + 2 ≠ 0 := by
    rw [← hα2]
    exact pow_ne_zero 2 hα0
  have ham2 : a - 2 ≠ 0 := by
    intro h0
    apply hsing
    have : a = 2 := by linear_combination h0
    rw [this]
    norm_num
  -- with `α² = a + 2`: `B² = (a+6)²/(4(a+2))`
  have hsq : ((a + 6) / (2 * α)) ^ 2 = (a + 6) ^ 2 / (4 * (a + 2)) := by
    rw [div_pow, mul_pow, hα2]
    norm_num
  have hden : (a + 6) ^ 2 / (4 * (a + 2)) - 4 = (a - 2) ^ 2 / (4 * (a + 2)) := by
    field_simp
    ring
  have hnum : (a + 6) ^ 2 / (4 * (a + 2)) - 3 = (a ^ 2 + 12) / (4 * (a + 2)) := by
    field_simp
    ring
  rw [hsq, hden, hnum]
  have hsq4 : a ^ 2 - 4 = (a - 2) * (a + 2) := by ring
  rw [hsq4]
  field_simp
  ring
