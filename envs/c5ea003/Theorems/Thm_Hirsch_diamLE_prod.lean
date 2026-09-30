-- Prove2me | Theorems.Thm_Hirsch_diamLE_prod
-- name    : Hirsch.diamLE_prod
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T06:34:50.159103+00:00
-- url     : https://prove2.me/theorems/724496a0-220f-4fe7-9b68-cf2b9be168cb
-- title:
--   Graph diameter of a Cartesian product is at most the sum of the factor diameters
-- statement:
--   **Diameter of a Cartesian product.** Let $P\subseteq E$ and $Q\subseteq F$ be subsets of real vector spaces, and suppose the vertex-edge graphs of $P$ and $Q$ have padded combinatorial diameters at most $B$ and $C$ respectively (in the sense of $\mathrm{DiamLE}$). Then the Cartesian product
--
--   $$
--   P\times Q=\bigl\{(x,y)\mid x\in P,\ y\in Q\bigr\}
--   $$
--
--   has padded combinatorial diameter at most $B+C$.
--
--   Extreme points of a product are pairs of extreme points. An edge of $P$ at a fixed extreme point of $Q$ remains an edge of the product (and symmetrically). Concatenating a $B$-step walk in the first factor with a $C$-step walk in the second therefore yields a product walk of length $B+C$. Empty factors make the statement vacuous.
--
--   This is the standard product formula for graph diameter. It does not bound $B$ or $C$ themselves, and it does not prove the unrestricted polynomial Hirsch conjecture. It packages the fact already used implicitly for boxes (products of intervals).
-- source:
--   Standard convex-geometry fact: diam(G(P)×G(Q)) = diam(G(P))+diam(G(Q)). Formalized for the Hirsch DiamLE predicate. Related: Hirsch.box_diameter_le_dimension is the interval-product special case.

import Mathlib
import Definitions.Def_Hirsch_model
set_option autoImplicit false
open Set Hirsch

namespace Hirsch

theorem diamLE_prod
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (P : Set E) (Q : Set F) (B C : ℕ)
    (hP : DiamLE P B) (hQ : DiamLE Q C) :
    DiamLE (P ×ˢ Q) (B + C) := by sorry

end Hirsch
