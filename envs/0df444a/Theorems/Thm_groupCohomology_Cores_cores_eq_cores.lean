-- Prove2me | Theorems.Thm_groupCohomology_Cores_cores_eq_cores
-- name    : groupCohomology.Cores.cores_eq_cores
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/5fa8cf91-a4df-53b3-a48c-6d77b15d762e
-- title:
--   Independence of the corestriction on H² from the transversal
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $A$ a $k$-linear representation of $G$, and $H \le G$ a subgroup of finite index. A `Cores.Transversal H` consists of a set-theoretic section $\sigma \colon G/H \to G$ of the projection $G \to G/H$, i.e. $\sigma(q) \bmod H = q$ for all $q$, which is normalised in the sense $\sigma(\bar 1) = 1$. For two such normalised transversals $\tau$ and $\tau'$, and for every class $x \in H^2(H, A)$ — where $A$ is regarded as a representation of $H$ by restriction along the inclusion $H \hookrightarrow G$ — the assertion is that $\operatorname{cores}_A(\tau)(x) = \operatorname{cores}_A(\tau')(x)$ in $H^2(G, A)$. Here $\operatorname{cores}_A(\tau)$ is the $k$-linear map $H^2(H,A) \to H^2(G,A)$ obtained by identifying $H^2(H,A)$ with the quotient of the module of $2$-cocycles by the $2$-coboundaries and descending the composite of the transversal-dependent cochain-level transfer $\tau \mapsto \mathrm{cor}_2^{\tau}$ on $2$-cocycles with the projection of $2$-cocycles onto $H^2(G,A)$, this descent being legitimate because coboundaries are sent to zero. Thus the two maps agree pointwise, hence are equal.
--
--   This is the classical statement that the transfer (corestriction) in group cohomology does not depend on the chosen system of coset representatives, here in degree $2$ and for the explicit cochain-level Eckmann transfer used in this development. It is what makes the notation $\operatorname{cores} \colon H^2(H,A) \to H^2(G,A)$ well defined, and it is used in establishing the compatibility of corestriction with restriction along conjugation, in the form of the expression of $\mathrm{res} \circ \mathrm{cores}$ as a finite sum of conjugated corestrictions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Cores_cores_eq_cores.lean

import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.Cores.cores_eq_cores
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex]
    (τ τ' : Cores.Transversal H) (x : H2 (Rep.res H.subtype A)) :
    Cores.cores A τ x = Cores.cores A τ' x := by sorry
