-- Prove2me | solution 1 for Fpy.equiv_reround
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:35:51.426559+00:00
-- url     : https://prove2.me/submissions/08c10b78-8f55-45d2-8887-93d0b74dd368

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_evalList_vars
import Theorems.Thm_P2M_Fpy_forall__of_evalList_3c5f4110a7e7
import Theorems.Thm_Fpy_Equiv_of_fwd
import Theorems.Thm_Fpy_Exec_withCtx_assign
import Theorems.Thm_Fpy_Val_isCtx_of_rnd


set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
namespace Fpy
theorem _root_.solution {Γ : AEnv D} {C C' : Val} {r r' : Num → Num} {c : Expr L} {x : Var}
    {op : L.ArithOp} {ys : List Var} (hc : Denotes Φ c C') (hr : C.rnd L = some r)
    (hr' : C'.rnd L = some r')
    (h : ∀ σ ns n, Γ.Holds σ → List.Forall₂ (fun y n => σ y = some (.num n)) ys ns →
      L.arith op ns = some n → r n = r' n) :
    Equiv Φ X Γ (some C) (.assign x (.arith op (ys.map .var)))
      (.withCtx c (.assign x (.arith op (ys.map .var)))) := by
  refine Equiv.of_fwd (fun σ C₀ o hΓ hκ hs => ?_) (fun σ C₀ _ _ hκ hs => ?_) <;>
    obtain rfl := hκ C rfl
  · cases hs with
    | assign he =>
      cases he with
      | arith hl hop hr₀ =>
        obtain rfl := Option.some.inj (hr₀.symm.trans hr)
        refine ⟨_, .withCtx ((hc σ C').mpr rfl) (Val.isCtx_of_rnd hr')
          (.assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr')), ?_⟩
        rw [h σ _ _ hΓ (forall₂_of_evalList hl) hop]
        exact Store.Agree.refl _
  · obtain ⟨_, _, he⟩ := hs.withCtx_assign
    cases he with
    | arith hl hop _ => exact ⟨_, .assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr)⟩
end Fpy
