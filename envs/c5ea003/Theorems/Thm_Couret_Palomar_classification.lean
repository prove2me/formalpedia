-- Prove2me | Theorems.Thm_Couret_Palomar_classification
-- name    : Couret.Palomar.classification
-- status  : Open
-- author  : @alexcour
-- created : 2026-11-19T21:22:18.449241+00:00
-- url     : https://prove2.me/theorems/7dcf21c6-0cf3-4b00-b853-09284897c18c
-- title:
--   Three-point ordered convolution-square classification
-- statement:
--   Let $G$ be an abelian group with decidable equality, and let $S,T\subseteq G$ be finite supports of size three. For $U\in\{S,T\}$ and $z\in G$, define $Q_U(z)=|\{(x,y)\in U\times U:x+y=z\}|$. The pairs are ordered and include the diagonal.
--
--   The equality $Q_S(z)=Q_T(z)$ for every $z\in G$ is equivalent to at least one of the following conditions.
--
--   1. There is $u\in G$ with $2u=0$ and $T=S+u$.
--   2. There are $a,b,d,u\in G$ with $d\ne0$, $2d=2u=0$, $2a\ne2b$, and $3(b-a)\in\{0,d\}$, such that $S=\{a,b,b+d\}$ and $T=\{a,2b-a,2b-a+d\}+u$.
--
--   Here $U+u=\{x+u:x\in U\}$. The classification applies also when $S=T$ and does not require the ambient group to be finite. The Lean statement uses the already-published STROBO definitions of the ordered square and both partner relations.
-- source:
--   Alexandre Couret, Palomar PALOMAR-2026-11-08-000010 v1, https://palomar-registry.org/entry?id=PALOMAR-2026-11-08-000010&version=1; https://github.com/alexcour/couret-finite-verifications/blob/24f69d5c2635ff405a628c170086a62d477fd3a5/Challenge.lean#L13-L38, Couret.Palomar.classification. Proof: Solution.lean at the same commit.

import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
set_option autoImplicit false

namespace Couret.Palomar

open Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem classification (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) :
    (∀ z : G, orderedSquare S z = orderedSquare T z) ↔
      OrdinaryPartner S T ∨ ExceptionalPartner S T := by sorry

end Couret.Palomar
