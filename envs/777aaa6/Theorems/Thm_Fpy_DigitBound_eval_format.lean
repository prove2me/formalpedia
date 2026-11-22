-- Prove2me | Theorems.Thm_Fpy_DigitBound_eval_format
-- name    : Fpy.DigitBound.eval_format
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:43:22.883036+00:00
-- url     : https://prove2.me/theorems/898ee917-6fe2-4017-885b-f1e4d85ad52e
-- title:
--   Digit Bound: eval format
-- statement:
--   **Theorem 4.2** (soundness of digit-bound analysis): with `p`, `q` and `k` bounding
--   the queries `max(msb − lsb + 1)`, `min(lsb)` and `max(msb)` over every constraint, a
--   finite value of `e` lies in `A(p, q, 2^(k+1) − 2^max(q, k − p + 1))`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L974-L987
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L974-L987

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.eval_format (hA : A.Sound Φ) {Δ : DEnv} {Γ : AEnv D} {κ : Option SCtx}
    {χ : Option Val} {Ψg Ψ Ψr : List Con} {n₀ n₁ n₂ : ℕ} {e : Expr (fpy decode)} {l m : Term}
    {τ : Option Term} (hd : DEval decode Φ A Δ Γ κ χ Ψg n₀ e (.num l m τ) Ψ n₁)
    (hFr : Fresh n₁ n₂ Ψr) {σ : Store} {C : Val} {ι : Asgn} {x : ℝ}
    (h : Eval Φ σ C e (.num (.finite x))) (hbg : Before n₀ Ψg) (hsg : Sat ι Ψg)
    (hΔ : Δ.Below n₀) (hκ : CtxBelow n₀ κ) (hσ : Δ.Holds Ψg ι σ) (hΓ : Γ.Holds σ)
    (hC : ∀ K ∈ κ, K.Admits ι C) (hχ : Admits χ C) {p : ℕ} {q k : ℤ}
    (hp : precBound (Ψg ++ Ψ ++ Ψr) l m ≤ ((p : ℤ) : EInt))
    (hq : (q : EInt) ≤ lsbBound (Ψg ++ Ψ ++ Ψr) l m) (hk : msbBound (Ψg ++ Ψ ++ Ψr) m ≤ k)
    (hqk : q ≤ k) (hp1 : 1 ≤ p) :
    (∃ c e' : ℤ, x = c * 2 ^ e' ∧ |c| < 2 ^ p) ∧ (∃ c : ℤ, x = c * 2 ^ q) ∧
      |x| ≤ 2 ^ (k + 1) - 2 ^ max q (k - p + 1) := by sorry
