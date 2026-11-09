-- Prove2me | Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
-- name    : Couret_OrbitLiftTranslation_2f31fa3b99fa
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:10:34.104405+00:00
-- url     : https://prove2.me/theorems/06baba2a-a2cb-4902-af41-074d3e584b7d
-- title:
--   Translated normal forms for order-two and order-four exchanges
-- statement:
--   Defines two translated support-pair forms in $\mathbb Z/(2m)\mathbb Z$. The first uses $2r=m$ and patterns $\{0,r,x,x+2r\}$ and $\{0,r,x+r,x+3r\}$. The second uses $4r=m$, common points selected from $\{2r,6r\}$ and $\{3r,7r\}$, and exchanged pairs $\{0,4r\}$ and $\{r,5r\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitLiftTranslation.lean; source file SHA-256 33597d5e925f18cae61682faf5b32c938e8ffa3afe5bd059b6d5d8d97af948df

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_OrbitLiftModels_210387863d55

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset

def TwoTranslated (m : ℕ) (S T : Finset (ZMod (2*m))) : Prop :=
  ∃ v x r : ZMod (2*m), r+r=m ∧
    S.image (fun z => z+v)={0,r,x,x+2 • r} ∧
    T.image (fun z => z+v)={0,r,x+r,x+3 • r}

def FourTranslated (m : ℕ) (S T : Finset (ZMod (2*m))) : Prop :=
  ∃ v r c d : ZMod (2*m), 4 • r=m ∧
    (c=2 • r ∨ c=6 • r) ∧ (d=3 • r ∨ d=7 • r) ∧
    S.image (fun z => z+v)={c,d,0,4 • r} ∧
    T.image (fun z => z+v)={c,d,r,5 • r}





end Couret.InterIA.Catalogue.Lifts


