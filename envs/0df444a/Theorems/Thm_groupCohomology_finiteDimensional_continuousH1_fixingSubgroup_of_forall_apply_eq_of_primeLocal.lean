-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_continuousH1_fixingSubgroup_of_forall_apply_eq_of_primeLocal
-- name    : groupCohomology.finiteDimensional_continuousH1_fixingSubgroup_of_forall_apply_eq_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/1db2f2fc-f7ca-5070-99e6-4bbb0f2366ff
-- title:
--   Finiteness of continuous H¹ for local K ni ζₚ
-- statement:
--   Let $p$ and $q$ be primes, and write $G_q$ for `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$. Let $K$ be an intermediate field of $\mathbb{Q}_q \subseteq$ `PadicAlgCl q` that is finite-dimensional over $\mathbb{Q}_q$ and contains an element $\zeta$ which is a primitive $p$-th root of unity. Let $H = K^{\mathrm{fix}} \le G_q$ be the fixing subgroup of $K$, and let $L$ be a representation of $H$ over $\mathbb{Z}/p$ such that $L.\rho\, s\, x = x$ for every $s \in H$ and every $x \in L$ (the action is trivial) and such that $\operatorname{finrank}_{\mathbb{Z}/p} L = 1$. Consider the group homomorphism $r$ obtained by composing the inclusion $H \hookrightarrow G_q$ with `primeLocalToGlobal q`, the map sending an automorphism of `PadicAlgCl q` over $\mathbb{Q}_q$ to its restriction to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` (restrict scalars to $\mathbb{Q}$, then restrict along normality). The conclusion is that the $\mathbb{Z}/p$-module `continuousH1 r L`, the image in $H^1(H, L)$ under the projection `H1π` of the submodule `levelCocycles₁ r L` of $1$-cocycles that are level-constant with respect to $r$, is finite-dimensional.
--
--   This is the base case of the finiteness of continuous $H^1$ with $\mathbb{F}_p$-coefficients at a finite place $q$: after a dévissage along a composition series and Shapiro's lemma, the coefficients are one-dimensional with trivial action over a finite extension $K/\mathbb{Q}_q$ containing $\zeta_p$, and finiteness is then Kummer theory for $K$. It is cited by [`groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal`](thm.html#groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_continuousH1_fixingSubgroup_of_forall_apply_eq_of_primeLocal.lean

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finiteDimensional_continuousH1_fixingSubgroup_of_forall_apply_eq_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ))) [FiniteDimensional ℚ_[(q : ℕ)] K]
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (L : Rep (ZMod p) ↥(K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)))
    (hL : ∀ (s : ↥(K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q))) (x : L), L.ρ s x = x)
    (h1 : Module.finrank (ZMod p) L = 1) :
    FiniteDimensional (ZMod p)
      (continuousH1 ((primeLocalToGlobal q).comp (K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)).subtype) L) := by sorry
