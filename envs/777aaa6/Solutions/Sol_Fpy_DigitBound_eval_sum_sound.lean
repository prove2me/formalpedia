-- Prove2me | solution 1 for Fpy.DigitBound.eval_sum_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:02.334193+00:00
-- url     : https://prove2.me/submissions/c2b73a9c-cfb1-4fa8-8ed8-b183a852885f

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
import Theorems.Thm_Fpy_DigitBound_sumVal_inRange
import Theorems.Thm_Fpy_DigitBound_AgreeOut_agree
import Theorems.Thm_Fpy_DigitBound_DescribesAll_mem
import Theorems.Thm_Fpy_DigitBound_Term_eval_congr
import Theorems.Thm_Fpy_DigitBound_eval_update
import Theorems.Thm_Fpy_DigitBound_fresh_numIn
import Theorems.Thm_Fpy_exec_sumBody
import Theorems.Thm_Fpy_exists_map_num


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
variable {D : FormatDomain} {A : Analysis (fpy decode) D}
namespace Fpy.DigitBound
theorem _root_.solution (hA : A.Sound Φ) (hsum : Φ "sum" = some ("xs", sumBody))
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
        (.num (.var (n₁ + 1)) (.var n₁) none) v := by
  cases h with
  | call hΦ he hs =>
    rw [hsum] at hΦ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ)
    obtain ⟨ι₁, a₁, hs₁, hdl⟩ := eval_sound hA hd he hbg hsg hΔ (ctxBelow_real _) hσ hΓ
      (admits_real' _) hχ
    cases hdl with
    | list hall =>
      rename_i vs
      have hel : ∀ w ∈ vs, ∃ u, w = .num u ∧ InRange (lo.eval ι₁) (hi.eval ι₁) u := by
        intro w hw
        obtain ⟨ι₀, h₀, hs₀, hd₀⟩ := hall.mem hw
        cases hd₀ with
        | num hu =>
          refine ⟨_, rfl, hu.imp id fun ⟨hl', hm', _⟩ => ?_⟩
          obtain ⟨b₁, b₂⟩ := hbnd ι₀ hs₀
          rw [Term.eval_congr h₀ hlo, Term.eval_congr h₀ hhi, hl', hm']
          exact ⟨b₁, b₂⟩
      obtain ⟨us, rfl, hus⟩ := exists_map_num hel
      obtain ⟨⟩ := exec_sumBody (r := id) rfl hs
      have hlen' := hlen σ _ he
      rw [List.length_map] at hlen'
      have hr := sumVal_inRange (by omega) hus
      rw [hlen'] at hr
      obtain ⟨ι₂, a₂, hs₂, hw⟩ := fresh_numIn (n := n₁)
        ((hlo.mono ha).mono (Nat.le_succ n₁)) (Hi := .add hi (.const ((Nat.clog 2 L : ℕ) : ℤ)))
        ⟨hhi.mono ha, trivial⟩ ι₁ _ fun hn => by
          obtain ⟨h₁, h₂⟩ := hr.resolve_left hn
          rw [eval_update (hlo.mono ha)]
          exact ⟨h₂, h₁⟩
      exact chain (DEval.wf hd).1 a₁ hs₁ a₂.agree hs₂ (.num hw)
end Fpy.DigitBound
