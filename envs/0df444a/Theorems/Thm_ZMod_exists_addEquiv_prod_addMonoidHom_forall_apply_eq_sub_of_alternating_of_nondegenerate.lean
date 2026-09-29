-- Prove2me | Theorems.Thm_ZMod_exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate
-- name    : ZMod.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/d204ef97-2d89-52ca-b2ce-f92f05fb6f6c
-- title:
--   Standard symplectic form on H(δ)× H(δ)
-- statement:
--   Fix natural numbers $g$ and $d$ and a function $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta(i)$ nonzero, and assume $\prod_i \delta(i) = d$. Write $H = \prod_{i} \mathbb{Z}/\delta(i)$ for the finite abelian group $(i : \mathrm{Fin}\,g) \to \mathbb{Z}/\delta(i)$, and let $K = H \times H$. Let $B : K \to K \to \mathbb{Z}/d$ be a function which is additive in its first argument ($B(a+b,c) = B(a,c)+B(b,c)$ for all $a,b,c$), additive in its second argument ($B(a,b+c) = B(a,b)+B(a,c)$), alternating in the sense that $B(a,a) = 0$ for all $a$, and non-degenerate in the sense that $B(a,b) = 0$ for all $b$ forces $a = 0$. The conclusion asserts the existence of an isomorphism of additive groups $$\alpha : H \times \operatorname{Hom}(H,\mathbb{Z}/d) \;\xrightarrow{\ \sim\ }\; H \times H = K$$ (the second factor being the group of additive homomorphisms $H \to \mathbb{Z}/d$) which carries $B$ to the standard pairing: for all $h, h' \in H$ and all $c, c' \in \operatorname{Hom}(H,\mathbb{Z}/d)$, $$B\bigl(\alpha(h,c),\,\alpha(h',c')\bigr) = c(h') - c'(h).$$
--
--   This is the symplectic normal form for a non-degenerate alternating $\mathbb{Z}/d$-valued pairing on a finite abelian group, specialised to the group $H(\delta)\times H(\delta)$ with $H(\delta) = \prod_i \mathbb{Z}/\delta(i)$ and $d = \prod_i \delta(i)$: such a pairing is always isometric to the canonical pairing between $H(\delta)$ and its $\mathbb{Z}/d$-dual. It is used in the construction of level structures on polarised abelian schemes, via [`AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_commutatorPairing_eq_pow`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_commutatorPairing_eq_pow), where the commutator pairing on a finite flat group scheme of the given type must be put into standard shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZMod_exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem ZMod.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) →
      (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d)
    (hadd₁ : ∀ a b c, B (a + b) c = B a c + B b c) (hadd₂ : ∀ a b c, B a (b + c) = B a b + B a c)
    (halt : ∀ a, B a a = 0) (hnd : ∀ a, (∀ b, B a b = 0) → a = 0) :
    ∃ α : (((i : Fin g) → ZMod (δ i)) × (((i : Fin g) → ZMod (δ i)) →+ ZMod d)) ≃+
        (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))),
      ∀ (h h' : (i : Fin g) → ZMod (δ i)) (c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d),
        B (α (h, c)) (α (h', c')) = c h' - c' h := by sorry
