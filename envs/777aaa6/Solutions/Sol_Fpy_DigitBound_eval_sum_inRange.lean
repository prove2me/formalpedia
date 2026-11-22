-- Prove2me | solution 1 for Fpy.DigitBound.eval_sum_inRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:00.558321+00:00
-- url     : https://prove2.me/submissions/6d00c1dd-1716-40f5-bfb9-261f542d99db

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
import Theorems.Thm_Fpy_DigitBound_sumVal_inRange
import Theorems.Thm_Fpy_exec_sumBody
import Theorems.Thm_Fpy_exists_map_num


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
namespace Fpy.DigitBound
theorem _root_.solution (hsum : Φ "sum" = some ("xs", sumBody)) {σ : Store}
    {e : Expr (fpy decode)} {lo hi : EInt} {L : ℕ} {v : Val} (hL : 1 ≤ L)
    (he : ∀ v₀, Eval Φ σ .real e v₀ →
      ∃ vs, v₀ = .list vs ∧ vs.length = L ∧ ∀ w ∈ vs, ∃ u, w = .num u ∧ InRange lo hi u)
    (h : Eval Φ σ .real (.call "sum" e) v) :
    ∃ u, v = .num u ∧ InRange lo (hi + ((Nat.clog 2 L : ℕ) : ℤ)) u := by
  cases h with
  | call hΦ he' hs =>
    rw [hsum] at hΦ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ)
    obtain ⟨vs, rfl, hlen, hws⟩ := he _ he'
    obtain ⟨us, rfl, hus⟩ := exists_map_num hws
    obtain ⟨⟩ := exec_sumBody (r := id) rfl hs
    rw [List.length_map] at hlen
    subst hlen
    exact ⟨_, rfl, sumVal_inRange hL hus⟩
end Fpy.DigitBound
