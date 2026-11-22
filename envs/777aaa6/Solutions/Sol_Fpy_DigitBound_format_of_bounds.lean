-- Prove2me | solution 1 for Fpy.DigitBound.format_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:11.855387+00:00
-- url     : https://prove2.me/submissions/51897e97-6b82-4b44-b1e5-2989283897a6

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
import Theorems.Thm_Fpy_DigitBound_precision_of_precBound
import Theorems.Thm_Fpy_DigitBound_quantum_of_lsbBound
import Theorems.Thm_Fpy_DigitBound_bound_of_msbBound

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {Ψ : List Con} {ι : Asgn} {l m : Term} {τ : Option Term} {x : ℝ}
namespace Fpy.DigitBound
theorem _root_.solution {p : ℕ} {e k : ℤ} (hs : Sat ι Ψ)
    (hd : Describes Ψ ι (.num l m τ) (.num (.finite x)))
    (hp : precBound Ψ l m ≤ ((p : ℤ) : EInt)) (he : (e : EInt) ≤ lsbBound Ψ l m)
    (hk : msbBound Ψ m ≤ k) (hek : e ≤ k) (hp1 : 1 ≤ p) :
    (∃ c e' : ℤ, x = c * 2 ^ e' ∧ |c| < 2 ^ p) ∧ (∃ c : ℤ, x = c * 2 ^ e) ∧
      |x| ≤ 2 ^ (k + 1) - 2 ^ max e (k - p + 1) := by
  refine ⟨precision_of_precBound hs hd hp, quantum_of_lsbBound hs hd he,
    bound_of_msbBound hs hd hk (max_le hek (by omega)) ?_⟩
  rcases le_total (k - p + 1) e with h | h
  · exact .inl (by rwa [max_eq_left h])
  · exact .inr (by rwa [max_eq_right h, show k - (k - p + 1) + 1 = (p : ℤ) by omega])
end Fpy.DigitBound
