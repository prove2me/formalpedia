-- Prove2me | Theorems.Thm_Couret_InterIA_QuotientBridge_pp_quotient_invariant
-- name    : Couret.InterIA.QuotientBridge.pp_quotient_invariant
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:32.066808+00:00
-- url     : https://prove2.me/theorems/c30cb641-d7a5-48f6-bf60-bdd32ed40b16
-- title:
--   Quotient invariance for paired differences
-- statement:
--   For every positive natural $m$, finite subset $C\subseteq R=\mathbb Z/(2m)\mathbb Z$, and $a,b\in R$, suppose $C$ is disjoint from both $\{a,a+m\}$ and $\{b,b+m\}$, and the finite sets $C\cup\{a,a+m\}$ and $C\cup\{b,b+m\}$ have equal ordered-pair sum counts everywhere. Then $X^{\pi(b-a)}F=F$ in $\mathbb Z[\mathbb Z/m\mathbb Z]$, where $\pi$ is reduction modulo $m$, $F=\sum_{c\in C}X^{\pi(c)}+X^{\pi(a)}+X^{\pi(b)}$, and $X^xX^y=X^{x+y}$. The set $C$ may be empty and $a=b$ is allowed.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientBridge.lean, lines 34–52; source file SHA-256 e3039f9ffa13d11690462eb5cb4b77969858bb42cad9a16ac2921936d5203630; theorem Couret.InterIA.QuotientBridge.pp_quotient_invariant

import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_IntersectionTwo_pp_actual_square_iff
import Definitions.Def_Couret_L4Assembly_154a326d9c14
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.QuotientBridge
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
open Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo Couret.InterIA.Projection

theorem pp_quotient_invariant (m : ℕ) (hm : 0 < m) (C : Finset (ZMod (2*m)))
    (a b : ZMod (2*m))
    (ha : Disjoint C (fibre (m : ZMod (2*m)) a))
    (hb : Disjoint C (fibre (m : ZMod (2*m)) b))
    (hsq : ∀ z, orderedSquare (C ∪ fibre (m : ZMod (2*m)) a) z =
      orderedSquare (C ∪ fibre (m : ZMod (2*m)) b) z) :
    atom (projection m (b-a)) * residual m C a b = residual m C a b := by sorry




section Moment
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







end Moment

















end Couret.InterIA.QuotientBridge
