-- Prove2me | Definitions.Def_Logic_DPCompletenessConstrained
-- name    : Logic_DPCompletenessConstrained
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:53:57.932962+00:00
-- url     : https://prove2.me/theorems/522834a9-85ea-4404-b115-06986016b4c1
-- title:
--   Aether Catalog definitions — Logic_DPCompletenessConstrained
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.DPCompletenessConstrained`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/DPCompletenessConstrained.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_DPCompleteness
/-
# Completeness without cancellativity, and constrained dynamic programming

In `Logic.DPCompleteness` the notion `IsDPRun` was *semantic* (all prefix scores are optimal)
and the existence of runs was proved using cancellativity of the weight monoid.  This file
removes that hypothesis by working with the *structural* (backtrace) notion of a run:

> `IsBacktrace D n f` : at each stage the DP recursion is realised on the nose,
> `val i (f i) + step i (f i) (f (i+1)) = val (i+1) (f (i+1))`.

The two notions turn out to be equivalent for **every** ordered weight monoid
(`isBacktrace_iff_isDPRun`), and completeness holds with no cancellativity assumption
(`dp_complete_general`).  This is exactly what is needed to cover **constrained** dynamic
programming, where infeasible transitions carry the absorbing weight `⊥` of `WithBot W` — a
monoid that is emphatically *not* cancellative.

As an application we characterise infeasibility (`val_eq_bot_iff`) and instantiate the theory on
the classical maximum-weight independent set problem on a path.
-/


namespace Logic.DPCompleteness

namespace DPSpec

/-! ## Structural runs -/

section General

variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]

/-- A *backtrace* run: at every stage the DP recursion is realised exactly. -/
def IsBacktrace (D : DPSpec S W) (n : ℕ) (f : ℕ → S) : Prop :=
  ∀ i < n, D.val i (f i) + D.step i (f i) (f (i + 1)) = D.val (i + 1) (f (i + 1))







end General

/-! ## Constrained dynamic programming over `WithBot` -/

section Constrained

variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]



end Constrained

/-! ## Application: maximum-weight independent set on a path -/

section MWIS

/-- Vertex weights of the running example: a path on stages `0,1,2,3,4`. -/
def misW : ℕ → ℤ
  | 0 => 3
  | 1 => 7
  | 2 => 2
  | 3 => 8
  | 4 => 1
  | _ => 0

/-- The maximum-weight-independent-set specification on a path.  The state at stage `i` records
whether vertex `i` is selected; selecting two adjacent vertices is forbidden, which is encoded
by the absorbing weight `⊥`. -/
def misD : DPSpec Bool (WithBot ℤ) where
  init b := if b then (misW 0 : WithBot ℤ) else (0 : WithBot ℤ)
  step i b c := if b && c then ⊥ else if c then (misW (i + 1) : WithBot ℤ) else (0 : WithBot ℤ)



end MWIS

end DPSpec

end Logic.DPCompleteness


