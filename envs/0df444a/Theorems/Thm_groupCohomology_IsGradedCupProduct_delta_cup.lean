-- Prove2me | Theorems.Thm_groupCohomology_IsGradedCupProduct_delta_cup
-- name    : groupCohomology.IsGradedCupProduct.delta_cup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/8fe39f48-6696-577f-ba36-e83997ff4c01
-- title:
--   Connecting map commutes with cup product in the first variable
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $X = (X_1 \to X_2 \to X_3)$ be a short complex of $k$-linear representations of $G$ which is short exact (`hX`). Let $B$ be a representation of $G$ such that the short complex obtained by tensoring $X$ on the right with $B$, $X_1 \otimes B \to X_2 \otimes B \to X_3 \otimes B$, is again short exact (`hXB`). Let $\mathrm{cup}_1$ be a graded cup family for the pair $(X_1, B)$, that is, a family of $k$-bilinear maps $H^p(G, X_1) \times H^q(G, B) \to H^{p+q}(G, X_1 \otimes B)$, and likewise $\mathrm{cup}_3$ for $(X_3, B)$; assume each satisfies `IsGradedCupProduct`, i.e. whenever $u$ is a $p$-cocycle and $v$ a $q$-cocycle whose cochain-level cup product $u \cup v$, given by $(u\cup v)(\sigma) = u(\sigma_{\mathrm{fst}}) \otimes \rho_B(\text{partial product of } \sigma_{\mathrm{fst}})\,v(\sigma_{\mathrm{snd}})$ on inhomogeneous cochains, is annihilated by the differential in degree $p+q$, the value of the family on the classes of $u$ and $v$ is the class of $u \cup v$. Then for all natural numbers $p, q$, all $x \in H^p(G, X_3)$ and all $y \in H^q(G, B)$, the connecting map of the tensored sequence from degree $p+q$ to degree $p+1+q$ sends $\mathrm{cup}_3\,p\,q\,x\,y$ to $\mathrm{cup}_1\,(p+1)\,q\,(\delta x)\,y$, where $\delta$ is the connecting map of $X$ from degree $p$ to degree $p+1$; the target degree is written $p+1+q$ so that no degree cast occurs.
--
--   This is the compatibility $\delta(x \cup y) = \delta(x) \cup y$ of the cup product with the connecting homomorphism in the first variable, for a short exact sequence of representations that remains exact after tensoring with $B$. It is used in the construction of the cup product on Tate cohomology and in the existence statement for Tate cup products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_IsGradedCupProduct_delta_cup.lean

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory groupCohomology

theorem groupCohomology.IsGradedCupProduct.delta_cup {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (B : Rep.{u} k G)
    (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact)
    (cup₁ : groupCohomology.GradedCupFamily X.X₁ B) (h₁ : groupCohomology.IsGradedCupProduct X.X₁ B cup₁)
    (cup₃ : groupCohomology.GradedCupFamily X.X₃ B) (h₃ : groupCohomology.IsGradedCupProduct X.X₃ B cup₃)
    (p q : ℕ) (x : groupCohomology X.X₃ p) (y : groupCohomology B q) :
    (groupCohomology.δ hXB (p + q) (p + 1 + q) (by omega)).hom (cup₃ p q x y)
      = cup₁ (p + 1) q ((groupCohomology.δ hX p (p + 1) rfl).hom x) y := by sorry
