-- Prove2me | Definitions.Def_Couret_Prelude_5b3cc8c481fb
-- name    : Couret_Prelude_5b3cc8c481fb
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:35.879075+00:00
-- url     : https://prove2.me/theorems/a34fba3c-e4d8-4191-8439-4ce4f59c8b44
-- title:
--   Labelled ordered-square counts and support transformations
-- statement:
--   For a finite abelian group $G$ and arbitrary finite supports $S,T\subseteq G$, define $$Q_S(w)=|\{(a,b)\in S^2:a+b=w\}|,\qquad\operatorname{SameSquare}(S,T)\iff\forall w,\ Q_S(w)=Q_T(w).$$ Ordered pairs retain every diagonal and multiplicity. The bundle also defines $G[2]=\{x:2x=0\}$, translation $S+k=\{x+k:x\in S\}$, and reflection $v-S=\{v-x:x\in S\}$. The raw support operations do not require cardinality three; that restriction belongs to later statements. This is the finite labelled-count vocabulary in namespace Couret.Strobo2Tors.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/Prelude.lean; source file SHA-256 89fcdc8c9910bcaf6db0f9ef8c7ab2a0a0f7b5e04fda098817c5e55b8bab0dc9

import Mathlib
import Mathlib

/-!
STROBO-2TORS: exact finite-abelian triple-support model.

Scope of this module: definitions and elementary two-torsion lemmas ONLY.
The universal collision classification and count are NOT formalized here.
Until a pinned Lean build succeeds, this source is UNCOMPILED.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Number of ORDERED representations of `w` as `a+b` with `a,b in S`,
including all diagonal pairs. -/
def orderedRep (S : Finset G) (w : G) : Nat :=
  ((S.product S).filter (fun p => p.1 + p.2 = w)).card

/-- Equality of ordered convolution squares with labels fixed. -/
def SameSquare (S T : Finset G) : Prop :=
  forall w : G, orderedRep S w = orderedRep T w

/-- Set of all elements killed by doubling. -/
def torsionTwo : Finset G :=
  Finset.univ.filter (fun x : G => x + x = 0)

/-- Translate a three-element generator set. -/
def translate (S : Finset G) (k : G) : Finset G :=
  S.image (fun x => x + k)

/-- Reflect a three-element generator set about `v`. -/
def reflect (S : Finset G) (v : G) : Finset G :=
  S.image (fun x => v - x)











end Couret.Strobo2Tors


