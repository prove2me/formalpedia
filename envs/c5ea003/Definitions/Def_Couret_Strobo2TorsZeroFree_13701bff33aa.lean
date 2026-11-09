-- Prove2me | Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
-- name    : Couret_Strobo2TorsZeroFree_13701bff33aa
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:48.29607+00:00
-- url     : https://prove2.me/theorems/fe3808d2-cbfc-462b-8a64-6f237fdd16b4
-- title:
--   Zero-containing and zero-free exceptional fibres
-- statement:
--   For a fibre $F$, define $F^\circ=\{S\in F:0\notin S\}$. Zero-containing exceptional supports generate the zero-hit exceptional fibres; the other exceptional fibres form the zero-missing family. The zero-free exceptional family is the image of all exceptional fibres under $F\mapsto F^\circ$.
--
--   These finite families distinguish whether zero deletion removes two supports or none, and provide the objects counted in the exceptional survival histogram.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]













def withoutZero (F : Finset (Finset G)) : Finset (Finset G) := F.filter (fun S => 0 ∉ S)











def zeroContainingExceptionalSupports : Finset (Finset G) :=
  (exceptionalSupports : Finset (Finset G)).filter (fun S => 0 ∈ S)

def zeroHitExceptionalFibres : Finset (Finset (Finset G)) :=
  (zeroContainingExceptionalSupports : Finset (Finset G)).image squareFibre

def zeroMissingExceptionalFibres : Finset (Finset (Finset G)) :=
  (exceptionalFibres : Finset (Finset (Finset G))) \ zeroHitExceptionalFibres































def zeroFreeExceptionalFibres : Finset (Finset (Finset G)) :=
  (exceptionalFibres : Finset (Finset (Finset G))).image withoutZero

















end Finite
end Couret.STROBO2TORS


