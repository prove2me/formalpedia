-- Prove2me | solution 1 for Fpy.equiv_bind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:04.566111+00:00
-- url     : https://prove2.me/submissions/cdf7dd93-a425-45de-b1d4-770786feae39

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_evalList_vars
import Theorems.Thm_P2M_Fpy_forall__updates_adf16c2a79da
import Theorems.Thm_Fpy_Store_agree_updates
import Theorems.Thm_Fpy_exec_binds
import Theorems.Thm_Fpy_Equiv_of_fwd
import Theorems.Thm_Fpy_EvalList_length_eq


set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
namespace Fpy
theorem _root_.solution (hA : A.Sound Φ) {Γ : AEnv D} {κ : Option Val} {x : Var} {op : L.ArithOp}
    {es : List (Expr L)} {ts : List Var} {as : List (AVal D)} {s' : Stmt L}
    (hts : ts.Nodup) (hl : ts.length = es.length) (hX : ∀ t ∈ ts, t ∈ X)
    (hes : ∀ e ∈ es, Avoids X e) (has : AEvalList A Φ Γ κ es as)
    (h : Equiv Φ X (updates Γ ts as) κ (.assign x (.arith op (ts.map .var))) s') :
    Equiv Φ X Γ κ (.assign x (.arith op es)) (Stmt.binds ts es s') := by
  have hvs {σ C vs} (hl' : EvalList Φ σ C es vs) :
      EvalList Φ (updates σ ts vs) C (ts.map .var) vs :=
    evalList_vars.mpr (forall₂_updates hts (hl.trans hl'.length_eq))
  refine Equiv.of_fwd (fun σ C o hΓ hκ hs => ?_) (fun σ C o' hΓ hκ hs => ?_)
  · cases hs with
    | assign he =>
      cases he with
      | arith hl' hop hr =>
        obtain ⟨o', hs', hag⟩ := (h (hΓ.updates (evalList_sound hA hl' hΓ hκ has)) hκ).1 _
          (.assign (.arith (hvs hl') hop hr))
        exact ⟨o', (exec_binds hl hX hes).mpr ⟨_, hl', hs'⟩,
          Outcome.Agree.trans (o₂ := .normal _) ((σ.agree_updates _ hX).update _ _) hag⟩
  · obtain ⟨vs, hl', hs'⟩ := (exec_binds hl hX hes).mp hs
    obtain ⟨_, ho, -⟩ := (h (hΓ.updates (evalList_sound hA hl' hΓ hκ has)) hκ).2 o' hs'
    cases ho with
    | assign he =>
      cases he with
      | arith hl'' hop hr =>
        obtain rfl := EvalList.det _ (hvs hl') hl''
        exact ⟨_, .assign (.arith hl' hop hr)⟩
end Fpy
