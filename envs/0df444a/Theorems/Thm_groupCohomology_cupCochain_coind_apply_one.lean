-- Prove2me | Theorems.Thm_groupCohomology_cupCochain_coind_apply_one
-- name    : groupCohomology.cupCochain_coind_apply_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/a8747221-90da-5d22-a59e-17a4289a2023
-- title:
--   Evaluation at 1 commutes with the cup cochain on coinduced modules
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $S \le G$ a subgroup, and let $A$, $B$, $N$ be $k$-linear representations of $S$. Let $\varphi \colon A \to_{k} (B \to_{k} N)$ be a $k$-bilinear map (no equivariance is assumed). Let $x \colon G \to \mathrm{coind}_{S\hookrightarrow G} A$ and $y \colon G \to \mathrm{coind}_{S \hookrightarrow G} B$ be arbitrary functions into the representations coinduced along the inclusion $S \hookrightarrow G$, whose underlying objects consist of functions $f \colon G \to A$ (resp. $G \to B$) satisfying the $S$-equivariance condition, with $G$ acting by right translation, and let $s, t \in S$. The assertion is that $$\varphi\bigl(x(s)(1)\bigr)\bigl(\bigl((\mathrm{coind}_{S\hookrightarrow G} B).\rho\,s\,(y(t))\bigr)(1)\bigr) = \mathrm{cupCochain}\,\varphi\,\bigl(u \mapsto x(u)(1)\bigr)\,\bigl(u \mapsto y(u)(1)\bigr)\,(s,t),$$ where, by definition of `cupCochain`, the right-hand side is $\varphi\bigl(x(s)(1)\bigr)\bigl(B.\rho\,s\,(y(t)(1))\bigr)$, the bidegree-$(1,1)$ cup-product cochain formed over $S$ from the two evaluated-at-$1$ functions $S \to A$ and $S \to B$.
--
--   This is the cochain-level compatibility of the cup product with the map "restrict to $S$ and evaluate at $1$" underlying Shapiro's lemma $H^i(G, \mathrm{coind}_S^G X) \cong H^i(S, X)$, in bidegree $(1,1)$. It is used in the proof of [`groupCohomology.bijective_theta_coind`](thm.html#groupCohomology.bijective_theta_coind).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_cupCochain_coind_apply_one.lean

import Mathlib
import Definitions.Def_GroupCohomology_CupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory
open groupCohomology

theorem groupCohomology.cupCochain_coind_apply_one
    {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
    {A B N : Rep.{u} k S} (φ : A →ₗ[k] B →ₗ[k] N)
    (x : G → Rep.coind S.subtype A) (y : G → Rep.coind S.subtype B) (s t : S) :
    φ ((x s : G → A) 1) (((Rep.coind S.subtype B).ρ s (y t) : G → B) 1)
      = cupCochain φ (fun u : S => (x u : G → A) 1) (fun u : S => (y u : G → B) 1) (s, t) := by sorry
