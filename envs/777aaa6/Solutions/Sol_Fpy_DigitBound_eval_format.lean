-- Prove2me | solution 1 for Fpy.DigitBound.eval_format
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:53:26.46212+00:00
-- url     : https://prove2.me/submissions/46859da7-3b44-46f3-8700-84fcb5866097

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
import Theorems.Thm_Fpy_DigitBound_format_of_bounds
import Theorems.Thm_Fpy_DigitBound_eval_solution

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (hA : A.Sound Φ) {Δ : DEnv} {Γ : AEnv D} {κ : Option SCtx}
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
      |x| ≤ 2 ^ (k + 1) - 2 ^ max q (k - p + 1) :=
  let ⟨_, hs, hv⟩ := eval_solution hA hd hFr h hbg hsg hΔ hκ hσ hΓ hC hχ
  format_of_bounds hs hv hp hq hk hqk hp1
end Fpy.DigitBound
