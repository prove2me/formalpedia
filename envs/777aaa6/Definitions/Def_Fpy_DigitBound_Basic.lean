-- Prove2me | Definitions.Def_Fpy_DigitBound_Basic
-- name    : Fpy_DigitBound_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:15:18.988395+00:00
-- url     : https://prove2.me/theorems/11d66cb8-115b-41ae-8f13-083dbbafe74f
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean

import Definitions.Def_Fpy_DigitBound_Defs
import Theorems.Thm_Fpy_DigitBound_Con_dep
import Theorems.Thm_Fpy_DigitBound_Term_eval_congr
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_withBound_b
import Theorems.Thm_Mpfx_Format_withBound_exp
import Theorems.Thm_Mpfx_Format_withBound_p
import Theorems.Thm_Mpfx_Format_withBound_specials
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_rnd_special
attribute [local simp] Mpfx.Dyadic.coe_abs
attribute [local simp] Mpfx.Dyadic.coe_half
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_rat_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_half
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_mul
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_sub
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.Dyadic.precisionAtMost_neg_iff
attribute [local simp] Mpfx.Dyadic.precisionAtMost_top
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_bot
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsEven.neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsOdd.neg_iff
attribute [local simp] Mpfx.FiniteFormat.extend_toFormat
attribute [local simp] Mpfx.FiniteFormat.isEven_zero
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_isUndefined
attribute [local simp] Mpfx.FiniteFormat.unbounded_p
attribute [local simp] Mpfx.FiniteFormat.unbounded_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_unbounded
attribute [local simp] Mpfx.Format.boundAfterNext_top
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Format.withBound_b
attribute [local simp] Mpfx.Format.withBound_exp
attribute [local simp] Mpfx.Format.withBound_p
attribute [local simp] Mpfx.Format.withBound_specials
attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special
attribute [local simp] Mpfx.rnd_special


set_option autoImplicit true
namespace Fpy.DigitBound
open Mpfx
theorem SCtx.Below.mono {n n' : ℕ} (h : n ≤ n') : ∀ {C : SCtx}, C.Below n → C.Below n'
  | .real, _ => trivial
  | .record _, hC => fun f hf => (hC f hf).mono h
mutual

theorem DVal.Below.mono {n n' : ℕ} (h : n ≤ n') : ∀ {d : DVal}, d.Below n → d.Below n'
  | .num _ _ _, ⟨hl, hm, hτ⟩ => ⟨hl.mono h, hm.mono h, fun t ht => (hτ t ht).mono h⟩
  | .list _ _, ⟨ha, hd⟩ => ⟨ha.trans h, DVal.Below.mono h hd⟩
  | .record _, hfs => DVal.BelowFields.mono h hfs
  | .other, _ => trivial
  | .ctx _, hC => SCtx.Below.mono h hC

theorem DVal.BelowFields.mono {n n' : ℕ} (h : n ≤ n') :
    ∀ {fs : List (Label × DVal)}, DVal.BelowFields n fs → DVal.BelowFields n' fs
  | [], _ => trivial
  | (_, _) :: _, ⟨hd, hfs⟩ => ⟨DVal.Below.mono h hd, DVal.BelowFields.mono h hfs⟩

end
theorem DEnv.Below.mono {n n' : ℕ} (h : n ≤ n') {Δ : DEnv} (hΔ : Δ.Below n) : Δ.Below n' :=
  fun x d hx => (hΔ x d hx).mono h
theorem RetBelow.mono {n n' : ℕ} (h : n ≤ n') {a : Option DVal} (ha : RetBelow n a) :
    RetBelow n' a := fun d hd => (ha d hd).mono h
theorem CtxBelow.mono {n n' : ℕ} (h : n ≤ n') {κ : Option SCtx} (hκ : CtxBelow n κ) :
    CtxBelow n' κ := fun C hC => (hκ C hC).mono h
theorem DVal.BelowFields.lookup {n : ℕ} {l : Label} {d : DVal} :
    ∀ {fs : List (Label × DVal)}, DVal.BelowFields n fs → fs.lookup l = some d → d.Below n
  | [], _, h => by simp [List.lookup] at h
  | (l', d') :: fs, ⟨hd, hfs⟩, h => by
    by_cases hl : l = l'
    · subst hl
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      exact h ▸ hd
    · have hne : (l == l') = false := by simpa using hl
      simp only [List.lookup, hne] at h
      exact DVal.BelowFields.lookup hfs h
theorem DEnv.Below.update {n : ℕ} {Δ : DEnv} (hΔ : Δ.Below n) (x : Var) {d : DVal}
    (hd : d.Below n) : (Δ.update x d).Below n := by
  intro z d' hz
  by_cases hzx : z = x
  · subst hzx
    simp only [DEnv.update, Function.update_self, Option.some.injEq] at hz
    exact hz ▸ hd
  · simp only [DEnv.update, Function.update_of_ne hzx] at hz
    exact hΔ z d' hz
theorem DEnv.Below.single {n : ℕ} {y : Var} {d : DVal} (hd : d.Below n) :
    (DEnv.single y d).Below n := by
  intro z d' hz
  by_cases hzy : z = y
  · subst hzy
    simp only [DEnv.single, if_pos, Option.some.injEq] at hz
    exact hz ▸ hd
  · simp [DEnv.single, hzy] at hz
theorem Agree.mono {n n' : ℕ} (h : n ≤ n') {ι ι' : Asgn} (hι : Agree n' ι ι') : Agree n ι ι' :=
  fun x hx => hι x (lt_of_lt_of_le hx h)
theorem Agree.trans {n : ℕ} {ι₁ ι₂ ι₃ : Asgn} (h₁ : Agree n ι₁ ι₂) (h₂ : Agree n ι₂ ι₃) :
    Agree n ι₁ ι₃ := fun x hx => (h₁ x hx).trans (h₂ x hx)
theorem Agree.refl (n : ℕ) (ι : Asgn) : Agree n ι ι := fun _ _ => rfl
theorem AgreeOut.trans {n₀ n₁ n₂ : ℕ} {ι₀ ι₁ ι₂ : Asgn} (h₀₁ : n₀ ≤ n₁) (h₁₂ : n₁ ≤ n₂)
    (a₁ : AgreeOut n₀ n₁ ι₀ ι₁) (a₂ : AgreeOut n₁ n₂ ι₁ ι₂) : AgreeOut n₀ n₂ ι₀ ι₂ := fun z hz => by
  rcases hz with hz | hz
  · rw [a₂ z (.inl (by omega)), a₁ z (.inl hz)]
  · rw [a₂ z (.inr hz), a₁ z (.inr (by omega))]
theorem NumIn.congr {n : ℕ} {ι ι' : Asgn} (h : Agree n ι ι') {l m : Term} {τ : Option Term}
    {u : Num} (hl : l.Below n) (hm : m.Below n) (hτ : ∀ t ∈ τ, t.Below n) (hu : NumIn ι l m τ u) :
    NumIn ι' l m τ u := by
  rcases hu with hu | ⟨hlu, hmu, htu⟩
  · exact .inl hu
  · refine .inr ⟨?_, ?_, fun t ht => ?_⟩
    · rw [hlu, Term.eval_congr h hl]
    · rw [hmu, Term.eval_congr h hm]
    · rw [htu t ht, Term.eval_congr h (hτ t ht)]
theorem SCtx.Admits.congr {n : ℕ} {ι ι' : Asgn} (h : Agree n ι ι') :
    ∀ {C : SCtx} {v : Val}, C.Below n → C.Admits ι v → C.Admits ι' v
  | .real, _, _, hv => hv
  | .record fs, _, hC, ⟨vs, rfl, hvs⟩ => by
    refine ⟨vs, rfl, ?_⟩
    revert hC
    induction hvs with
    | nil => exact fun _ => .nil
    | cons hfw _ ih =>
      intro hC
      refine .cons ⟨hfw.1, ?_⟩ (ih fun f hf => hC f (List.mem_cons_of_mem _ hf))
      rw [← Term.eval_congr h (hC _ (List.mem_cons_self ..))]
      exact hfw.2
theorem Sat.append {ι : Asgn} {Ψ Ψ' : List Con} (h : Sat ι Ψ) (h' : Sat ι Ψ') :
    Sat ι (Ψ ++ Ψ') := fun c hc => (List.mem_append.mp hc).elim (h c) (h' c)
theorem Fresh.nil (n : ℕ) : Fresh n n [] :=
  ⟨le_rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
theorem Fresh.le {n₀ n₁ : ℕ} {Ψ : List Con} (h : Fresh n₀ n₁ Ψ) : n₀ ≤ n₁ := h.1
theorem Fresh.single (n : ℕ) {c : Con} (hc : c.head = n) : Fresh n (n + 1) [c] :=
  ⟨Nat.le_succ n, List.nodup_singleton _, fun c' h => by
    obtain rfl := List.mem_singleton.mp h
    omega⟩
theorem Fresh.append {n₀ n₁ n₂ : ℕ} {Ψ Ψ' : List Con} (h : Fresh n₀ n₁ Ψ) (h' : Fresh n₁ n₂ Ψ') :
    Fresh n₀ n₂ (Ψ ++ Ψ') := by
  obtain ⟨h₀₁, hn, hr⟩ := h
  obtain ⟨h₁₂, hn', hr'⟩ := h'
  refine ⟨h₀₁.trans h₁₂, ?_, fun c hc => ?_⟩
  · rw [List.map_append]
    refine List.Nodup.append hn hn' (List.disjoint_left.mpr fun _ hx hx' => ?_)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c', hc', he⟩ := List.mem_map.mp hx'
    have := (hr c hc).2
    have := (hr' c' hc').1
    omega
  · rcases List.mem_append.mp hc with hc | hc
    · exact ⟨(hr c hc).1, by have := (hr c hc).2; omega⟩
    · exact ⟨by have := (hr' c hc).1; omega, (hr' c hc).2⟩
theorem Sat.extend {n₀ n₁ : ℕ} {Ψ : List Con} (hΨ : Fresh n₀ n₁ Ψ) (ι : Asgn) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ := by
  -- Downward induction on `j`: the constraints with heads below `j` hold.
  have key : ∀ k j, n₁ - j = k → ∀ ι : Asgn, (∀ c ∈ Ψ, c.head < j → c.P ι) →
      ∃ ι', Agree j ι ι' ∧ Sat ι' Ψ := by
    intro k
    induction k with
    | zero =>
      intro j hj ι hι
      exact ⟨ι, Agree.refl _ _, fun c hc => hι c hc (by have := (hΨ.2.2 c hc).2; omega)⟩
    | succ k ih =>
      intro j hj ι hι
      by_cases hc : ∃ c ∈ Ψ, c.head = j
      · obtain ⟨c, hcΨ, rfl⟩ := hc
        obtain ⟨z, hz⟩ := c.sat ι
        obtain ⟨ι', hι', hs⟩ := ih (c.head + 1) (by omega) (Function.update ι c.head z) (by
          intro c' hc' hlt
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
          · exact c'.dep (fun x hx => (Function.update_of_ne (by omega) _ _).symm) (hι c' hc' hlt)
          · obtain rfl : c' = c := List.inj_on_of_nodup_map hΨ.2.1 hc' hcΨ heq
            exact hz)
        refine ⟨ι', fun x hx => ?_, hs⟩
        rw [← hι' x (by omega), Function.update_of_ne (by omega)]
      · obtain ⟨ι', hι', hs⟩ := ih (j + 1) (by omega) ι (fun c' hc' hlt => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
          · exact hι c' hc' hlt
          · exact absurd ⟨c', hc', heq⟩ hc)
        exact ⟨ι', Agree.mono (Nat.le_succ j) hι', hs⟩
  exact key _ n₀ rfl ι fun c hc hlt => absurd (hΨ.2.2 c hc).1 (by omega)
theorem Fresh.before {n₀ n₁ : ℕ} {Ψ : List Con} (h : Fresh n₀ n₁ Ψ) : Before n₁ Ψ :=
  fun c hc => (h.2.2 c hc).2
theorem Before.append {n₀ n₁ : ℕ} {Ψ Ψ' : List Con} (hΨ : Before n₀ Ψ) (h : Fresh n₀ n₁ Ψ') :
    Before n₁ (Ψ ++ Ψ') := fun c hc =>
  (List.mem_append.mp hc).elim (fun hc => lt_of_lt_of_le (hΨ c hc) h.le) (h.before c)
theorem Sat.congr {n : ℕ} {Ψ : List Con} (hΨ : Before n Ψ) {ι ι' : Asgn}
    (h : Agree n ι ι') (hs : Sat ι Ψ) : Sat ι' Ψ := fun c hc =>
  c.dep (fun x hx => h x (lt_of_le_of_lt hx (hΨ c hc))) (hs c hc)
mutual

/-- A description under `ι` holds under any `ι'` agreeing below `n`,
with constraints on fresh variables from `n` added: each list element's
assignment re-chooses those variables. -/
theorem Describes.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ') :
    ∀ {ι ι' : Asgn} {d : DVal} {v : Val}, Agree n ι ι' → Describes Ψ ι d v → d.Below n →
      Describes (Ψ ++ Ψ') ι' d v
  | _, _, _, _, h, .num hu, ⟨hl, hm, hτ⟩ => .num (hu.congr h hl hm hτ)
  | _, _, _, _, h, .list hall, ⟨ha, hd⟩ => .list (DescribesAll.grow hb hF h hall ha hd)
  | _, _, _, _, h, .record hfs, hbs => .record (DescribesFields.grow hb hF h hfs hbs)
  | _, _, _, _, _, .bool, _ => .bool
  | _, _, _, _, _, .real, _ => .real
  | _, _, _, _, _, .ctxv, _ => .ctxv
  | _, _, _, _, h, .sctx hC, hbC => .sctx (hC.congr h hbC)

theorem DescribesAll.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ') :
    ∀ {ι ι' : Asgn} {d : DVal} {a : ℕ} {vs : List Val}, Agree n ι ι' →
      DescribesAll Ψ ι d a vs → a ≤ n → d.Below n → DescribesAll (Ψ ++ Ψ') ι' d a vs
  | _, _, _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, _, h, .cons (ι' := ι₀) h₀ hs hd tl, ha, hdb => by
    obtain ⟨ι₁, a₁, hs₁⟩ := Sat.extend hF ι₀
    exact .cons (fun x hx => (h x (lt_of_lt_of_le hx ha)).symm.trans
        ((h₀ x hx).trans (a₁ x (lt_of_lt_of_le hx ha))))
      ((Sat.congr hb a₁ hs).append hs₁) (Describes.grow hb hF a₁ hd hdb)
      (DescribesAll.grow hb hF h tl ha hdb)

theorem DescribesFields.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ)
    (hF : Fresh n n' Ψ') :
    ∀ {ι ι' : Asgn} {afs : List (Label × DVal)} {fs : List (Label × Val)}, Agree n ι ι' →
      DescribesFields Ψ ι afs fs → DVal.BelowFields n afs → DescribesFields (Ψ ++ Ψ') ι' afs fs
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, h, .cons hd hfs, ⟨hb₁, hbs⟩ =>
    .cons (Describes.grow hb hF h hd hb₁) (DescribesFields.grow hb hF h hfs hbs)

end
theorem DEnv.without_eq_some {Δ : DEnv} {X : List Var} {x : Var} {d : DVal} :
    Δ.without X x = some d ↔ x ∉ X ∧ Δ x = some d := by
  unfold DEnv.without; split <;> simp_all
theorem DEnv.Below.without {n : ℕ} {Δ : DEnv} (hΔ : Δ.Below n) (X : List Var) :
    (Δ.without X).Below n := fun x d hx => hΔ x d (DEnv.without_eq_some.mp hx).2
theorem DEnv.Holds.update {Δ : DEnv} {Ψ : List Con} {ι : Asgn} {σ : Store}
    (hσ : Δ.Holds Ψ ι σ) (x : Var) {d : DVal} {v : Val} (hd : Describes Ψ ι d v) :
    (Δ.update x d).Holds Ψ ι (σ.update x v) := by
  intro z d' hz
  by_cases hzx : z = x
  · subst hzx
    simp only [DEnv.update, Function.update_self, Option.some.injEq] at hz
    exact ⟨v, by simp [Store.update], hz ▸ hd⟩
  · simp only [DEnv.update, Function.update_of_ne hzx] at hz
    simpa [Store.update, Function.update_of_ne hzx] using hσ z d' hz
local notation "nan" => (WithSpecial.special Special.nan : Num)
def Within (Ψ : List Con) (ι : Asgn) (Δ' : DEnv) (a : Option DVal) : Outcome → Prop
  | .normal σ => Δ'.Holds Ψ ι σ
  | .ret v => ∃ d ∈ a, Describes Ψ ι d v
end Fpy.DigitBound


