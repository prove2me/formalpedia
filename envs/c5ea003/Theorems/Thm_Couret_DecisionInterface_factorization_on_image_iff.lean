-- Prove2me | Theorems.Thm_Couret_DecisionInterface_factorization_on_image_iff
-- name    : Couret.DecisionInterface.factorization_on_image_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T17:02:10.642003+00:00
-- url     : https://prove2.me/theorems/b145d39a-3151-4894-b905-9428fddaa6d8
-- title:
--   Factorization through the observed image
-- statement:
--   For arbitrary universe levels $u,v,w$, types $X:\operatorname{Type}_u$, $Y:\operatorname{Type}_v$ and $A:\operatorname{Type}_w$, and functions $O:X\to Y$ and $D:X\to A$, the following are equivalent: there exists a function $f:I_O\to A$ such that $f(O(x),\text{a witness that }O(x)\in O(X))=D(x)$ for every $x\in X$, where $I_O=\{y\in Y:\exists x\in X,\ O(x)=y\}$ is the subtype of observed values; and for all $x,y\in X$, $O(x)=O(y)$ implies $D(x)=D(y)$. No inhabitedness, decidable equality, or finiteness is assumed. In particular $X$ may be empty, in which case $I_O$ is empty, both universal conditions are vacuous, and a function from $I_O$ to $A$ exists even when $A$ is empty; no extension of $f$ to all of $Y$ is asserted.
-- source:
--   Alexandre Couret, Observation, Reconstruction and Justified Decisions: A unified Couret research manuscript, companion v0.2 (2026), https://zenodo.org/records/23981308; archive Couret_Unified_Companion_v02_20261105.zip, SHA-256 ec2e5a91aa13da8b8bf4aef44bc28ccfb4074b2d257edf942053afe928d53154; file studies/query_cost/DecisionInterface.lean, lines 56–66, theorem Couret.DecisionInterface.factorization_on_image_iff

import Definitions.Def_Couret_DecisionInterface_d4e860afd684
import Init

/- Source-only draft: NOT compiled in this package. No `sorry` placeholders.
   This module states the logical interface, not the cost/parity theorem.
   No connection to the Python implementation is formally proved here. -/
set_option autoImplicit false

universe u v w t
namespace Couret.DecisionInterface
variable {X : Type u} {Y : Type v} {A : Type w} {B : Type t}

theorem factorization_on_image_iff (O : X → Y) (D : X → A) :
    (∃ f : ObservedImage O → A,
      ∀ x : X, f ⟨O x, ⟨x, rfl⟩⟩ = D x) ↔ FibreConstant O D := by sorry




end Couret.DecisionInterface
