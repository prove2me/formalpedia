-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_continuousH2_fixingSubgroup_of_forall_apply_eq_of_primeLocal
-- name    : groupCohomology.finiteDimensional_continuousH2_fixingSubgroup_of_forall_apply_eq_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/04af6fa4-ddb2-5c4a-a6a3-6dfec03534f7
-- title:
--   Finite-dimensionality of continuous H² of a trivial mod p line
-- statement:
--   Let $p$ be a prime and $q$ a prime, and let $K$ be an intermediate field of the algebraic closure $\overline{\mathbb{Q}}_q$ of $\mathbb{Q}_q$ over $\mathbb{Q}_q$ which is finite-dimensional over $\mathbb{Q}_q$ and contains an element $\zeta$ that is a primitive $p$-th root of unity. Write $G$ for the fixing subgroup of $K$ inside the group $\operatorname{Aut}_{\mathbb{Q}_q}(\overline{\mathbb{Q}}_q)$ of $\mathbb{Q}_q$-algebra automorphisms of $\overline{\mathbb{Q}}_q$, this last group being `primeLocalGaloisGroup q`. Let $L$ be a representation of $G$ on a $\mathbb{Z}/p$-module such that every $s \in G$ acts as the identity on $L$, and such that $\operatorname{finrank}_{\mathbb{Z}/p} L = 1$. Let $r$ be the homomorphism obtained by composing the inclusion $G \hookrightarrow \operatorname{Aut}_{\mathbb{Q}_q}(\overline{\mathbb{Q}}_q)$ with `primeLocalToGlobal q`, which sends an automorphism to its restriction of scalars to $\mathbb{Q}$ followed by restriction to the normal subextension $\overline{\mathbb{Q}}$; the levels for continuous cohomology are thus pulled back along this global restriction map. Then the $\mathbb{Z}/p$-module $\mathrm{continuousH2}\,r\,L$, the quotient of the module `levelCocycles₂ r L` of level $2$-cocycles by the submodule of those which are level $2$-coboundaries, is finite-dimensional over $\mathbb{Z}/p$.
--
--   This is the local finiteness input at a prime $q$ for the deformation-theoretic bookkeeping: for a finite extension $K/\mathbb{Q}_q$ containing $\mu_p$ and a trivial one-dimensional mod $p$ coefficient module, the continuous $H^2$ of the absolute Galois group of $K$ is finite-dimensional, the classical reason being that it is the $p$-torsion of the Brauer group of $K$, of dimension one. It is used by [`groupCohomology.finiteDimensional_continuousH2_of_isOpen_of_primeLocal`](thm.html#groupCohomology.finiteDimensional_continuousH2_of_isOpen_of_primeLocal), which passes from a fixing subgroup of a finite level to an arbitrary open subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_continuousH2_fixingSubgroup_of_forall_apply_eq_of_primeLocal.lean

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finiteDimensional_continuousH2_fixingSubgroup_of_forall_apply_eq_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ))) [FiniteDimensional ℚ_[(q : ℕ)] K]
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (L : Rep (ZMod p) ↥(K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)))
    (hL : ∀ (s : ↥(K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q))) (x : L), L.ρ s x = x)
    (h1 : Module.finrank (ZMod p) L = 1) :
    FiniteDimensional (ZMod p)
      (continuousH2 ((primeLocalToGlobal q).comp (K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)).subtype) L) := by sorry
