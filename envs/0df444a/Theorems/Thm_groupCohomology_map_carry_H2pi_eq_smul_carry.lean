-- Prove2me | Theorems.Thm_groupCohomology_map_carry_H2pi_eq_smul_carry
-- name    : groupCohomology.map_carry_H2pi_eq_smul_carry
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/24cd0dd7-f379-53e4-9841-d48228a99dff
-- title:
--   Restriction multiplies a carry class by f/gcd(ord s,f)
-- statement:
--   Let $G$ and $H$ be groups, $j : H \to G$ an injective group homomorphism, and let $s \in G$ be an element of finite order such that every element of $G$ lies in the subgroup of integer powers of $s$; let $f$ be a natural number and $t \in H$ an element of finite order such that $j(t) = s^{f}$ and every element of $H$ lies in the subgroup of integer powers of $t$. Let $A$ be a $\mathbb{Z}$-linear representation of $G$, $B$ one of $H$, and $\varphi$ a morphism of representations of $H$ from the restriction $\mathrm{res}_j A$ to $B$. Let $a \in A$ be fixed by the action of $s$. For a generator as above, $\mathrm{carryFun}$ denotes the $2$-cochain sending $(g_1,g_2)$ to $a$ when $\mathrm{ord}(s) \le \ell(g_1) + \ell(g_2)$ and to $0$ otherwise, where $\ell(g) \in \{0,\dots,\mathrm{ord}(s)-1\}$ is the discrete logarithm of $g$ to base $s$ obtained from the bijection $\mathrm{Fin}(\mathrm{ord}\,s) \simeq \langle s \rangle$; likewise over $H$ with $t$ and $\varphi(a)$. Assuming both of these cochains are $2$-cocycles, the map on $H^{2}$ induced by the pair $(j,\varphi)$ in degree $2$ carries the class of the first carry cocycle to $\bigl(f / \gcd(\mathrm{ord}(s), f)\bigr)$ times the class of the second, the scalar being a natural-number quotient acting by $\bullet$ on $H^{2}(H,B)$.
--
--   This is the cocycle-level form, for explicit "carry" classes on finite cyclic groups, of the statement that restriction to a subgroup of index-related degree multiplies the invariant of a class by the corresponding multiplicity, as in $\mathrm{inv}_L \circ \mathrm{res} = [L:K]\cdot \mathrm{inv}_K$. It is used in the computation of local invariants and in the Herbrand-quotient arguments attached to idelic Artin maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_carry_H2pi_eq_smul_carry.lean

import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.map_carry_H2pi_eq_smul_carry {G : Type} [Group G] {H : Type} [Group H] (j : H →* G) (hj : Function.Injective j)
    (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfins : IsOfFinOrder s)
    (f : ℕ) (t : H) (hjt : j t = s ^ f) (ht : ∀ h : H, h ∈ Subgroup.zpowers t) (hfint : IsOfFinOrder t)
    (A : Rep ℤ G) (B : Rep ℤ H) (φ : Rep.res j A ⟶ B)
    (a : A) (ha : A.ρ s a = a)
    (hza : carryFun s hs hfins a ∈ cocycles₂ A)
    (hzb : carryFun t ht hfint (φ.hom a) ∈ cocycles₂ B) :
    (groupCohomology.map j φ 2).hom ((H2π A).hom ⟨carryFun s hs hfins a, hza⟩) =
      (f / Nat.gcd (orderOf s) f) • (H2π B).hom ⟨carryFun t ht hfint (φ.hom a), hzb⟩ := by sorry
