-- Prove2me | solution 1 for denote_substTerm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:25:33.975552+00:00
-- url     : https://prove2.me/submissions/29657a89-7945-4d77-95a8-6e4e70bf4f36

import Mathlib
import Definitions.Def_Bridges_PosetTheory_HigherOrderEqSat
open HOType HOTerm Var in
theorem solution {Γ Δ : Ctx} {τ : HOType}
    (s : Subst Γ Δ) (t : HOTerm Γ τ)
    (envΔ : Env Δ) (envΓ : Env Γ)
    (henv : ∀ {α : HOType} (x : Var Γ α),
      denote (s x) envΔ = lookupVar x envΓ) :
    denote (substTerm s t) envΔ = denote t envΓ := by
  -- renaming lemma (needed for the weakening inside `Subst.ext`)
  have hren : ∀ {Γ Δ : Ctx} {τ : HOType} (ρren : Renaming Γ Δ) (t : HOTerm Γ τ)
      (envΔ : Env Δ) (envΓ : Env Γ),
      (∀ {α : HOType} (x : Var Γ α), lookupVar (ρren x) envΔ = lookupVar x envΓ) →
        denote (renameTerm ρren t) envΔ = denote t envΓ := by
    intro Γ Δ τ ρren t envΔ envΓ henv
    induction t generalizing Δ with
    | var x => exact henv x
    | lam body ih =>
      show (fun a => denote (renameTerm ρren.ext body) (envΔ, a)) = (fun a => denote body (envΓ, a))
      funext a
      refine ih ρren.ext (envΔ, a) (envΓ, a) (fun x => ?_)
      cases x with
      | vz => rfl
      | vs x => exact henv x
    | app f arg ihf iharg =>
      show denote (renameTerm ρren f) envΔ (denote (renameTerm ρren arg) envΔ)
        = denote f envΓ (denote arg envΓ)
      rw [ihf ρren envΔ envΓ henv, iharg ρren envΔ envΓ henv]
  induction t generalizing Δ with
  | var x => exact henv x
  | lam body ih =>
    show (fun a => denote (substTerm s.ext body) (envΔ, a)) = (fun a => denote body (envΓ, a))
    funext a
    refine ih s.ext (envΔ, a) (envΓ, a) (fun x => ?_)
    cases x with
    | vz => rfl
    | vs x =>
      show denote (renameTerm (fun y => .vs y) (s x)) (envΔ, a) = lookupVar x envΓ
      rw [hren (fun y => .vs y) (s x) (envΔ, a) envΔ (fun y => rfl)]
      exact henv x
  | app f arg ihf iharg =>
    show denote (substTerm s f) envΔ (denote (substTerm s arg) envΔ)
      = denote f envΓ (denote arg envΓ)
    rw [ihf s envΔ envΓ henv, iharg s envΔ envΓ henv]
