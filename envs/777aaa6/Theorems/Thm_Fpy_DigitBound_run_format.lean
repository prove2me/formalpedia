-- Prove2me | Theorems.Thm_Fpy_DigitBound_run_format
-- name    : Fpy.DigitBound.run_format
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:42.875342+00:00
-- url     : https://prove2.me/theorems/ba6cae36-85b4-4fc2-b377-bd6a3557f84f
-- title:
--   Digit Bound: run format
-- statement:
--   **Soundness over both analyses**: in a run of the program from an argument
--   described by `d` (and by `a` for format inference), every finite value of a
--   visited expression lies in the format of the program's queries.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Reach.lean#L269-L287
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Reach.lean#L269-L287

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Reach
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_single

set_option autoImplicit true
open Fpy Fpy.DigitBound
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
variable (decode Φ A) (t : Site decode D)
variable {decode Φ A t}

theorem Fpy.DigitBound.run_format (hA : A.Sound Φ) {y : Var} {s : Stmt (fpy decode)} {d d' : DVal}
    {a : AVal D} {Δ' : DEnv} {Ψ : List Con} {n₀ n₁ : ℕ} {v : Val} {ι : Asgn}
    (hr : SReach decode Φ A t (.single y d) (.single y a) (some .real) (some .real) [] n₀ s Δ'
      (some d') Ψ n₁ (.single y v) .real)
    (hd : d.Below n₀) (hv : Describes [] ι d v) (ha : Fpy.Describes a v) {l m : Term}
    {τ : Option Term} (ht : t.d = .num l m τ) {x : ℝ} (h : Eval Φ t.σ t.C t.e (.num (.finite x)))
    {p : ℕ} {q k : ℤ} (hp : precBound Ψ l m ≤ ((p : ℤ) : EInt))
    (hq : (q : EInt) ≤ lsbBound Ψ l m) (hk : msbBound Ψ m ≤ k) (hqk : q ≤ k) (hp1 : 1 ≤ p) :
    (∃ c e' : ℤ, x = c * 2 ^ e' ∧ |c| < 2 ^ p) ∧ (∃ c : ℤ, x = c * 2 ^ q) ∧
      |x| ≤ 2 ^ (k + 1) - 2 ^ max q (k - p + 1) := by sorry
