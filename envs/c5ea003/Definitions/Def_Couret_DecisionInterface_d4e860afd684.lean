-- Prove2me | Definitions.Def_Couret_DecisionInterface_d4e860afd684
-- name    : Couret_DecisionInterface_d4e860afd684
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T17:01:56.411267+00:00
-- url     : https://prove2.me/theorems/0917b4c7-68f6-4ead-b9fc-e0666e27ddc8
-- title:
--   Observation fibres and decision functions
-- statement:
--   For arbitrary universe levels $u,v,w,t$, let $X:\operatorname{Type}_u$, $Y:\operatorname{Type}_v$, $A:\operatorname{Type}_w$ and $B:\operatorname{Type}_t$, allowing empty types. For $O:X\to Y$ and $y\in Y$, the fibre is the predicate $O(x)=y$ on $X$. Refining a predicate $C$ by a function $q:X\to B$ at $b\in B$ gives the predicate $C(x)\land q(x)=b$. A decision $a\in A$ is known on $C$ when every $x$ satisfying $C$ has $D(x)=a$, for $D:X\to A$; this is vacuous if $C$ has no members. Fibre constancy of $D$ relative to $O$ means $O(x)=O(y)$ implies $D(x)=D(y)$ for every $x,y\in X$. The observed image is the subtype of $y\in Y$ for which some $x\in X$ satisfies $O(x)=y$. On that subtype, the induced decision selects such an input using classical choice and returns its value under $D$. This definition itself requires no fibre-constancy hypothesis, so agreement with every input in a fibre is a separate property. If $X$ is empty, its observed image is empty, and the induced function still has that empty domain even if $A$ is empty.
-- source:
--   Alexandre Couret, Observation, Reconstruction and Justified Decisions: A unified Couret research manuscript, companion v0.2 (2026), https://zenodo.org/records/23981308; archive Couret_Unified_Companion_v02_20261105.zip, SHA-256 ec2e5a91aa13da8b8bf4aef44bc28ccfb4074b2d257edf942053afe928d53154; file studies/query_cost/DecisionInterface.lean

import Init

/- Source-only draft: NOT compiled in this package. No `sorry` placeholders.
   This module states the logical interface, not the cost/parity theorem.
   No connection to the Python implementation is formally proved here. -/
set_option autoImplicit false

universe u v w t
namespace Couret.DecisionInterface
variable {X : Type u} {Y : Type v} {A : Type w} {B : Type t}

def Fibre (O : X → Y) (y : Y) : X → Prop := fun x => O x = y

def Refine (C : X → Prop) (q : X → B) (b : B) : X → Prop :=
  fun x => C x ∧ q x = b

def KnownDecision (C : X → Prop) (D : X → A) (a : A) : Prop :=
  ∀ x, C x → D x = a

def FibreConstant (O : X → Y) (D : X → A) : Prop :=
  ∀ x y, O x = O y → D x = D y

def ObservedImage (O : X → Y) := {y : Y // ∃ x : X, O x = y}













noncomputable def inducedDecision (O : X → Y) (D : X → A)
    (y : ObservedImage O) : A := D (Classical.choose y.property)







end Couret.DecisionInterface


