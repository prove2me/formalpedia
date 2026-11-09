-- Prove2me | Definitions.Def_Couret_AffineSupportForms_4a272694daca
-- name    : Couret_AffineSupportForms_4a272694daca
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:10:57.401386+00:00
-- url     : https://prove2.me/theorems/89544555-7d1e-4097-9e63-66285b460f0f
-- title:
--   Affine normal forms for cyclic support pairs
-- statement:
--   For supports $S,T\subseteq\mathbb Z/(2m)\mathbb Z$, this defines two simultaneous affine-normal-form predicates using a unit multiplier and a common translation. The two-lift form requires $2m=4q$, $q>0$, and images $\{0,q,x,x+2q\}$ and $\{0,q,x+q,x+3q\}$. The four-lift form requires $2m=8q$, $q>0$, common entries $c\in\{2q,6q\}$, $d\in\{3q,7q\}$, and images $\{c,d,0,4q\}$ and $\{c,d,q,5q\}$.
--
--   These predicates express catalogue cases up to one shared affine change of coordinates.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineSupportForms.lean; source file SHA-256 113669caaf57f6ebef75a308ce77f0622fd86334394df6458d63f094203eafc4

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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts

def TwoAffineForm (m : ℕ) (S T : Finset (ZMod (2*m))) : Prop :=
  ∃ q : ℕ, 0 < q ∧ 2*m=4*q ∧ ∃ u : (ZMod (2*m))ˣ, ∃ v x : ZMod (2*m),
    S.image (fun z => (u : ZMod (2*m))*z+v)={0,(q : ZMod (2*m)),x,x+2 • (q : ZMod (2*m))} ∧
    T.image (fun z => (u : ZMod (2*m))*z+v)={0,(q : ZMod (2*m)),x+q,x+3 • (q : ZMod (2*m))}

def FourAffineForm (m : ℕ) (S T : Finset (ZMod (2*m))) : Prop :=
  ∃ q : ℕ, 0 < q ∧ 2*m=8*q ∧ ∃ u : (ZMod (2*m))ˣ, ∃ v c d : ZMod (2*m),
    (c=2 • (q : ZMod (2*m)) ∨ c=6 • (q : ZMod (2*m))) ∧
    (d=3 • (q : ZMod (2*m)) ∨ d=7 • (q : ZMod (2*m))) ∧
    S.image (fun z => (u : ZMod (2*m))*z+v)={c,d,0,4 • (q : ZMod (2*m))} ∧
    T.image (fun z => (u : ZMod (2*m))*z+v)={c,d,(q : ZMod (2*m)),5 • (q : ZMod (2*m))}







end Couret.InterIA.Catalogue.Affine


