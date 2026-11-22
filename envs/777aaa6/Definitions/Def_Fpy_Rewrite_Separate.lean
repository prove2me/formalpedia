-- Prove2me | Definitions.Def_Fpy_Rewrite_Separate
-- name    : Fpy_Rewrite_Separate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:30:36.6142+00:00
-- url     : https://prove2.me/theorems/497f1a6e-3a1e-44da-92fd-c85e970d81d0
-- title:
--   Separate
-- statement:
--   Definitions and structural lemmas for Separate, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
set_option autoImplicit true
namespace Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
def DenotesAt (Φ : Program L) (σ : Store) (c : Expr L) (C : Val) : Prop :=
  ∀ v, Eval Φ σ .real c v ↔ v = C
def Denotes (Φ : Program L) (c : Expr L) (C : Val) : Prop := ∀ σ, DenotesAt Φ σ c C
def FmtsIn (Γ : AEnv D) (ys : List Var) (Fs : List D.Fmt) : Prop :=
  List.Forall₂ (fun y F => ∃ a, Γ y = some a ∧ D.γ a.toFmt ⊆ D.γ F) ys Fs
def updates {α : Type} (f : Var → Option α) : List Var → List α → Var → Option α
  | t :: ts, x :: xs => updates (Function.update f t (some x)) ts xs
  | _, _ => f
theorem AEnv.Holds.updates {Γ : AEnv D} {σ : Store} (hΓ : Γ.Holds σ) :
    ∀ {ts : List Var} {as : List (AVal D)} {vs : List Val}, List.Forall₂ Describes as vs →
      AEnv.Holds (Fpy.updates Γ ts as) (Fpy.updates σ ts vs)
  | [], _, _, _ | _ :: _, _, _, .nil => hΓ
  | _ :: _, _, _, .cons hd hs => (hΓ.update _ hd).updates hs
def Stmt.binds : List Var → List (Expr L) → Stmt L → Stmt L
  | t :: ts, e :: es, s => .seq (.assign t e) (Stmt.binds ts es s)
  | _, _, s => s
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}
section Split
variable {c₁ c₂ : RoundCtx} (hS : c₂.S.Composes c₁.S c₁.O c₁.rm) (hb : c₂.F.b = ⊤)
include hS hb
end Split
end Fpy


