-- Prove2me | Theorems.Thm_Fpy_DigitBound_eval_solution
-- name    : Fpy.DigitBound.eval_solution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:43:20.461053+00:00
-- url     : https://prove2.me/theorems/e782e27d-219b-4760-99ab-35cb7c6e399e
-- title:
--   Digit Bound: eval solution
-- statement:
--   Constraint soundness for any expression: an evaluation of `e` gives a solution of
--   every constraint, those before `e` (`Ψg`), from `e` (`Ψ`) and after it (`Ψr`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L959-L969
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L959-L969

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.eval_solution (hA : A.Sound Φ) {Δ : DEnv} {Γ : AEnv D} {κ : Option SCtx}
    {χ : Option Val} {Ψg Ψ Ψr : List Con} {n₀ n₁ n₂ : ℕ} {e : Expr (fpy decode)} {d : DVal}
    (hd : DEval decode Φ A Δ Γ κ χ Ψg n₀ e d Ψ n₁) (hFr : Fresh n₁ n₂ Ψr) {σ : Store}
    {C : Val} {ι : Asgn} {v : Val} (h : Eval Φ σ C e v) (hbg : Before n₀ Ψg) (hsg : Sat ι Ψg)
    (hΔ : Δ.Below n₀) (hκ : CtxBelow n₀ κ) (hσ : Δ.Holds Ψg ι σ) (hΓ : Γ.Holds σ)
    (hC : ∀ K ∈ κ, K.Admits ι C) (hχ : Admits χ C) :
    ∃ ι', Sat ι' (Ψg ++ Ψ ++ Ψr) ∧ Describes (Ψg ++ Ψ ++ Ψr) ι' d v := by sorry
