-- Prove2me | Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
-- name    : Couret_QuarterPatterns_d02dd43ea8cd
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:11:54.689205+00:00
-- url     : https://prove2.me/theorems/03189865-214b-400a-a01b-831e9c9859c5
-- title:
--   Quarter-period support patterns
-- statement:
--   For $q\ge0$ and $x\in\mathbb Z/(4q)$, define $$A_q(x)=\{0,q,x,x+2q\},\qquad B_q(x)=\{0,q,x+q,x+3q\}.$$ The excluded parameter set is $\{0,q,2q,3q\}$. The raw definitions allow $q=0$ and degenerate parameters; nondegeneracy is imposed by later theorems.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPatterns.lean; source file SHA-256 9b8c9c084f6777ce5ceb009e93059cec597e0b75776aa3c220bc02c5f8961a7b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter
open Finset Couret.InterIA.Catalogue.Parameters Couret.InterIA.Parity

def patternA (q : ℕ) (x : ZMod (4*q)) : Finset (ZMod (4*q)) :=
  {0,(q : ZMod (4*q)),x,x+2 • (q : ZMod (4*q))}

def patternB (q : ℕ) (x : ZMod (4*q)) : Finset (ZMod (4*q)) :=
  {0,(q : ZMod (4*q)),x+q,x+3 • (q : ZMod (4*q))}

def badParameters (q : ℕ) : Finset (ZMod (4*q)) := {0,(q : ZMod (4*q)),2 • (q : ZMod (4*q)),3 • (q : ZMod (4*q))}





















end Couret.InterIA.Catalogue.Quarter


