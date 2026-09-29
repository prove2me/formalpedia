-- Prove2me | Theorems.Thm_groupCohomology_IsGradedCupProduct_cup_delta
-- name    : groupCohomology.IsGradedCupProduct.cup_delta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/d815f947-2706-5e89-9647-499aff58cf56
-- title:
--   Connecting map and cup product in the second variable
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $A$ a $k$-linear representation of $G$, and let $X$ be a short complex $X_1 \to X_2 \to X_3$ of representations. Assume $X$ is short exact (`hX`) and that its image under $A \otimes -$, i.e. the short complex $A \otimes X_1 \to A \otimes X_2 \to A \otimes X_3$, is short exact as well (`hAX`). Let $\mathrm{cup}_1$ be a family of $k$-bilinear maps $H^p(G,A) \times H^q(G,X_1) \to H^{p+q}(G, A \otimes X_1)$ and $\mathrm{cup}_3$ a family $H^p(G,A) \times H^q(G,X_3) \to H^{p+q}(G,A\otimes X_3)$, each assumed to be a graded cup product in the sense that whenever $x$, $y$ are inhomogeneous cocycles of degrees $p$, $q$ and the cochain $\mathrm{cochainCup}$ of their underlying cochains — $(\sigma \mapsto x(\sigma_{\text{first }p}) \otimes \rho(\text{partial product})\, y(\sigma_{\text{last }q}))$ — is again a cocycle, the value of the family on the classes of $x$ and $y$ is the class of that cochain. Then for all $p, q$ and all $x \in H^p(G,A)$, $y \in H^q(G,X_3)$, the connecting map $\delta$ of the tensored sequence in degrees $p+q \to p+q+1$ sends $\mathrm{cup}_3\,p\,q\,x\,y$ to $(-1)^p \cdot \mathrm{cup}_1\,p\,(q+1)\,x\,(\delta_X y)$, where $\delta_X$ is the connecting map of $X$ in degrees $q \to q+1$.
--
--   This is the Leibniz-type compatibility of the cup product with the connecting homomorphism in the second variable, the companion of the corresponding formula in the first variable. It is used in the construction of the cup product on Tate cohomology by dimension shifting, being cited by [`Rep.IsTateCupProduct.cup_mk_right_eq_tateMap`](thm.html#Rep.IsTateCupProduct.cup_mk_right_eq_tateMap) and [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_IsGradedCupProduct_cup_delta.lean

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory groupCohomology

theorem groupCohomology.IsGradedCupProduct.cup_delta {k G : Type u} [CommRing k] [Group G]
    (A : Rep.{u} k G) {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (cup₁ : groupCohomology.GradedCupFamily A X.X₁) (h₁ : groupCohomology.IsGradedCupProduct A X.X₁ cup₁)
    (cup₃ : groupCohomology.GradedCupFamily A X.X₃) (h₃ : groupCohomology.IsGradedCupProduct A X.X₃ cup₃)
    (p q : ℕ) (x : groupCohomology A p) (y : groupCohomology X.X₃ q) :
    (groupCohomology.δ hAX (p + q) (p + q + 1) rfl).hom (cup₃ p q x y)
      = ((-1 : k) ^ p) • cup₁ p (q + 1) x ((groupCohomology.δ hX q (q + 1) rfl).hom y) := by sorry
