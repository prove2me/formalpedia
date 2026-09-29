-- Prove2me | Theorems.Thm_groupCohomology_exists_isLocalBridge1
-- name    : groupCohomology.exists_isLocalBridge1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/7d8da30f-2c75-5dc9-9044-b63f4d8077c3
-- title:
--   Existence of the degree-one local bridge map
-- statement:
--   Let $\pi\colon H\to D$ be a homomorphism of groups, and let $R\xrightarrow{f}P\xrightarrow{g}B$ be morphisms of $\mathbb Z$-linear representations of $D$ such that the underlying additive maps are exact at $P$ (in the sense of `Function.Exact`, i.e. the image of $f$ is the kernel of $g$) and $g$ is surjective on underlying modules. Let $X$ be a $\mathbb Z$-linear representation of $D$, $A$ a $\mathbb Z$-linear representation of $H$, and $\iota\colon X\to A$ an injective additive map which is $\pi$-equivariant, $\iota(\rho_X(\pi h)x)=\rho_A(h)\iota(x)$ for all $h\in H$, $x\in X$. Let $p$ be a natural number, $M$ a $\mathbb Z/p$-linear representation of $H$, and $\kappa\colon B\times M\to A$ a biadditive pairing which is $\pi$-equivariant, $\kappa(\rho_B(\pi h)b,\rho_M(h)m)=\rho_A(h)\kappa(b,m)$, and perfect in the strong sense that every additive map $c\colon B\to A$ equals $\kappa(\cdot,m)$ for a unique $m\in M$. Assume finally the divisibility hypothesis that for every morphism $\varphi\colon R\to X$ of representations of $D$ there is an element $\psi$ of the internal hom object $\operatorname{Hom}(\pi^*P,A)$ in representations of $H$ whose underlying linear map satisfies $\psi(f(x))=\iota(\varphi(x))$ for all $x\in R$. Then there exists an additive map $\Lambda$ from the group of $D$-morphisms $R\to X$ to $H^1(H,M)$ satisfying the predicate `IsLocalBridge₁` for the data $\pi,f,g,\iota,\kappa$.
--
--   This is the cochain-level construction, in degree one, of the bridge map attached to a perfect pairing and a divisible coefficient module that underlies Tate-duality style local computations: an equivariant $\varphi\colon R\to X$ is extended along $f$ to an additive map $P\to A$, and the resulting $1$-cocycle is read back into $M$ through $\kappa$. It is applied at the archimedean and $p$-adic places in [`NumberField.InfPlaceDecomp.exists_isLocalBridge1_archimedean`](thm.html#NumberField.InfPlaceDecomp.exists_isLocalBridge1_archimedean) and [`NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl`](thm.html#NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl), and in the continuity statement [`groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two`](thm.html#groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isLocalBridge1.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_LocalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_isLocalBridge1
    {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {X : Rep ℤ D} {A : Rep ℤ H} (ι : X →+ A) (hι : Function.Injective ι)
    (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
    {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)
    (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hdiv : ∀ φ : R ⟶ X, ∃ ψ : (ihom (Rep.res π P)).obj A, ∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ.hom x)) :
    ∃ Λ : (R ⟶ X) →+ H1 M, IsLocalBridge₁ π f g ι κ Λ := by sorry
