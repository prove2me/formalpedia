-- Prove2me | Theorems.Thm_Fpy_DigitBound_eval_sum_sound
-- name    : Fpy.DigitBound.eval_sum_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:45:50.413717+00:00
-- url     : https://prove2.me/theorems/1714400c-e42d-4188-b2d6-01616272d9b1
-- title:
--   Digit Bound: eval sum sound
-- statement:
--   **D-Sum**, over the analysis: a list summary bounded by `lo` and `hi` under
--   the constraints so far gives `sum(e)` the fresh interval `[n₁ + 1, n₁]` with
--   `lo ≤ λ` and `μ ≤ hi + ⌈log₂ L⌉`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L146-L191
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L146-L191

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
variable {D : FormatDomain} {A : Analysis (fpy decode) D}

theorem Fpy.DigitBound.eval_sum_sound (hA : A.Sound Φ) (hsum : Φ "sum" = some ("xs", sumBody))
    {Δ : DEnv} {Γ : AEnv D} {χ : Option Val} {Ψg Ψ : List Con} {n₀ n₁ a : ℕ}
    {e : Expr (fpy decode)} {l m lo hi : Term} {τ : Option Term} {L : ℕ}
    (hd : DEval decode Φ A Δ Γ (some .real) χ Ψg n₀ e (.list (.num l m τ) a) Ψ n₁)
    (hlo : lo.Below a) (hhi : hi.Below a) (ha : a ≤ n₁)
    (hbnd : ∀ ι, Sat ι (Ψg ++ Ψ) → lo.eval ι ≤ l.eval ι ∧ m.eval ι ≤ hi.eval ι) (hL : 1 ≤ L)
    (hlen : ∀ σ vs, Eval Φ σ .real e (.list vs) → vs.length = L) {σ : Store} {v : Val}
    {ι : Asgn} (h : Eval Φ σ .real (.call "sum" e) v) (hbg : Before n₀ Ψg) (hsg : Sat ι Ψg)
    (hΔ : Δ.Below n₀) (hσ : Δ.Holds Ψg ι σ) (hΓ : Γ.Holds σ) (hχ : Admits χ .real) :
    ∃ ι', Agree n₀ ι ι' ∧
      Sat ι' (Ψ ++ bounds n₁ lo (.add hi (.const ((Nat.clog 2 L : ℕ) : ℤ)))
        ((hlo.mono ha).mono (Nat.le_succ n₁)) ⟨hhi.mono ha, trivial⟩) ∧
      Describes (Ψg ++ (Ψ ++ bounds n₁ lo (.add hi (.const ((Nat.clog 2 L : ℕ) : ℤ)))
        ((hlo.mono ha).mono (Nat.le_succ n₁)) ⟨hhi.mono ha, trivial⟩)) ι'
        (.num (.var (n₁ + 1)) (.var n₁) none) v := by sorry
