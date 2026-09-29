-- Prove2me | solution 1 for denote_renameTerm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:20:45.661207+00:00
-- url     : https://prove2.me/submissions/2428688a-4d43-4da3-9abc-3fbc251362fd

import Mathlib
import Definitions.Def_Bridges_PosetTheory_HigherOrderEqSat
open HOType HOTerm Var in
theorem solution {Γ Δ : Ctx} {τ : HOType}
    (ρren : Renaming Γ Δ) (t : HOTerm Γ τ)
    (envΔ : Env Δ) (envΓ : Env Γ)
    (henv : ∀ {α : HOType} (x : Var Γ α),
      lookupVar (ρren x) envΔ = lookupVar x envΓ) :
    denote (renameTerm ρren t) envΔ = denote t envΓ := by
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
