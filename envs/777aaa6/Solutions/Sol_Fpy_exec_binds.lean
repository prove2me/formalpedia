-- Prove2me | solution 1 for Fpy.exec_binds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:37:15.182094+00:00
-- url     : https://prove2.me/submissions/c67c4757-4f26-412a-93dc-e45deda72436

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_Store_agree_update_of_mem


set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
namespace Fpy
theorem _root_.solution {C : Val} {s : Stmt L} {o : Outcome} :
    ∀ {σ : Store} {ts : List Var} {es : List (Expr L)}, ts.length = es.length →
      (∀ t ∈ ts, t ∈ X) → (∀ e ∈ es, Avoids X e) →
      (Exec Φ σ C (Stmt.binds ts es s) o ↔
        ∃ vs, EvalList Φ σ C es vs ∧ Exec Φ (updates σ ts vs) C s o)
  | _, [], [], _, _, _ =>
    ⟨fun h => ⟨[], .nil, h⟩, fun ⟨_, hl, h⟩ => by cases hl; exact h⟩
  | σ, t :: ts, e :: es, hl, hX, ha => by
    have hX' := fun t ht => hX t (List.mem_cons_of_mem _ ht)
    have ha' := fun e he => ha e (List.mem_cons_of_mem _ he)
    have hagree := fun v => σ.agree_update_of_mem (hX t (List.mem_cons_self ..)) v
    constructor
    · intro h
      cases h with
      | seqNormal h₁ h₂ =>
        cases h₁ with
        | assign he =>
          obtain ⟨vs, hl', h⟩ := (solution (Nat.succ.inj hl) hX' ha').mp h₂
          exact ⟨_ :: vs, .cons he (hl'.agree (hagree _).symm ha'), h⟩
      | seqRet h₁ => cases h₁
    · rintro ⟨_, hl', h⟩
      cases hl' with
      | cons he hl' =>
        exact .seqNormal (.assign he)
          ((solution (Nat.succ.inj hl) hX' ha').mpr ⟨_, hl'.agree (hagree _) ha', h⟩)
end Fpy
