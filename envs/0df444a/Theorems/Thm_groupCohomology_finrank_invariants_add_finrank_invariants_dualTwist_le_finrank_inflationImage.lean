-- Prove2me | Theorems.Thm_groupCohomology_finrank_invariants_add_finrank_invariants_dualTwist_le_finrank_inflationImage
-- name    : groupCohomology.finrank_invariants_add_finrank_invariants_dualTwist_le_finrank_inflationImage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/ac4a5a90-41b1-516e-b133-fd9e689ab95f
-- title:
--   Depth bound: h⁰(M)+h⁰(M^∨(χ)) at most the inflation image
-- statement:
--   Let $k$ be a field, $G$ a group, $M$ a representation of $G$ over $k$ that is finite-dimensional, and $\chi : G \to k^\times$ a character. Let $U, W, I$ be normal subgroups of $G$, with $U$ and $W$ of finite index, such that $\rho_M$ is trivial on $U$, $U \le W$ and $W \le I \vee U$. Let $q$ be a prime that is invertible in $k$ (i.e. $q \neq 0$ in $k$) and assume every $w \in W$ has some $q$-power $w^{q^a} \in U$. Let $t \in I$ be such that every $i \in I$ satisfies $(t^a)^{-1} i \in W$ for some $a \in \mathbb{N}$, and let $\varphi \in G$ be such that every $g \in G$ satisfies $(\varphi^n)^{-1} g \in I \vee U$ for some $n \in \mathbb{N}$. Assume $\chi$ is trivial on $I$ and on $U$ and $\chi(\varphi) = q$ in $k$, and let $m \in \mathbb{N}$ satisfy $mq = 1$ in $k$. In $G/W$, writing $\bar{t}, \bar{\varphi}$ for the images of $t, \varphi$, assume $\bar{\varphi}^{-1} \bar{t} \bar{\varphi} = \bar{t}^{m}$ and $\bar{\varphi} \bar{t} \bar{\varphi}^{-1} \in \langle \bar{t} \rangle$ (the subgroup of integer powers of $\bar{t}$). Let $S$ be the image of $I$ in $G/W$ under $\mathrm{mk}'\,W$, assume $(G/W)/S$ is finite, put $f$ for the order of the class of $\bar{\varphi}$ in $(G/W)/S$, and let $j \in \mathbb{N}$ satisfy $\bar{\varphi}^{f} = \bar{t}^{j}$. Four vanishing conditions are imposed on $A = M^{W}$, viewed as a representation of $G/W$: $\sum_{i<\mathrm{ord}(\bar{t})} \rho_A(\bar{t}^{i}) = 0$, $\sum_{i<j} \rho_A(\bar{t}^{i}) = 0$, $\sum_{i<f} \rho_A(\bar{\varphi}^{i}) = 0$, and the norm of the representation of $(G/W)/S$ on $A^{S}$ is $0$. Then $$\dim_k M^{G} + \dim_k \bigl(M^{\vee}(\chi)\bigr)^{G} \le \dim_k \operatorname{im}\bigl(H^1(G/U, M^{U}) \to H^1(G, M)\bigr),$$ where $M^{\vee}(\chi)$ is the dual representation with $g$ acting by $\chi(g)$ times the dual of $\rho_M(g)$, and the right-hand side is the range of the inflation map in degree $1$ along $G \to G/U$ together with the canonical $G$-map $M^{U} \to M$.
--
--   This is the inequality in the direction $h^0(M) + h^0(M^{\vee}(\chi)) \le \dim H^1$ of the local Euler-characteristic count at a residue characteristic $q$ invertible in $k$, formulated at a fixed level: the cohomology is measured by the inflation image from $G/U$, and the hypotheses describe a tame quotient with tame generator $t$ and Frobenius $\varphi$ together with depth (norm-vanishing) conditions on $M^{W}$. It feeds the bound [`groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses`](thm.html#groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses) on continuous classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_invariants_add_finrank_invariants_dualTwist_le_finrank_inflationImage.lean

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_TateTwist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u

theorem groupCohomology.finrank_invariants_add_finrank_invariants_dualTwist_le_finrank_inflationImage
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (χ : G →* kˣ)
    (U W I : Subgroup G) [U.Normal] [W.Normal] [I.Normal] [U.FiniteIndex] [W.FiniteIndex]
    (hU : ∀ u ∈ U, M.ρ u = 1) (hUW : U ≤ W) (hWI : W ≤ I ⊔ U)
    (q : ℕ) [Fact q.Prime] (hq : (q : k) ≠ 0) (hW : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
    (t : G) (ht : t ∈ I) (htame : ∀ i ∈ I, ∃ a : ℕ, (t ^ a)⁻¹ * i ∈ W)
    (φ : G) (hgen : ∀ g, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ I ⊔ U)
    (hχI : ∀ i ∈ I, χ i = 1) (hχU : ∀ u ∈ U, χ u = 1) (hχφ : (χ φ : k) = q)
    (m : ℕ) (hmq : (m : k) * q = 1)
    (hm : (QuotientGroup.mk φ : G ⧸ W)⁻¹ * QuotientGroup.mk t * QuotientGroup.mk φ
      = (QuotientGroup.mk t : G ⧸ W) ^ m)
    (hst : (QuotientGroup.mk φ : G ⧸ W) * QuotientGroup.mk t * (QuotientGroup.mk φ)⁻¹
      ∈ Subgroup.zpowers (QuotientGroup.mk t : G ⧸ W))

    [Fintype ((G ⧸ W) ⧸ I.map (QuotientGroup.mk' W))] (j : ℕ)
    (hrel : (QuotientGroup.mk φ : G ⧸ W) ^ orderOf (QuotientGroup.mk (QuotientGroup.mk φ : G ⧸ W) :
        (G ⧸ W) ⧸ I.map (QuotientGroup.mk' W)) = (QuotientGroup.mk t : G ⧸ W) ^ j)
    (hNt : ∑ i ∈ Finset.range (orderOf (QuotientGroup.mk t : G ⧸ W)),
        (M.quotientToInvariants W).ρ ((QuotientGroup.mk t : G ⧸ W) ^ i) = 0)
    (hNj : ∑ i ∈ Finset.range j, (M.quotientToInvariants W).ρ ((QuotientGroup.mk t : G ⧸ W) ^ i) = 0)
    (hNφ : ∑ i ∈ Finset.range (orderOf (QuotientGroup.mk (QuotientGroup.mk φ : G ⧸ W) :
        (G ⧸ W) ⧸ I.map (QuotientGroup.mk' W))),
        (M.quotientToInvariants W).ρ ((QuotientGroup.mk φ : G ⧸ W) ^ i) = 0)
    (hN : ((M.quotientToInvariants W).quotientToInvariants (I.map (QuotientGroup.mk' W))).ρ.norm = 0) :
    finrank k M.ρ.invariants + finrank k (M.dualTwist χ).ρ.invariants
      ≤ finrank k (inflationImage M U) := by sorry
