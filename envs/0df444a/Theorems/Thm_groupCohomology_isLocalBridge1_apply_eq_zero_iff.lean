-- Prove2me | Theorems.Thm_groupCohomology_isLocalBridge1_apply_eq_zero_iff
-- name    : groupCohomology.isLocalBridge1_apply_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/1cccaf44-fe89-5d05-b7a0-7dc333a9bbf4
-- title:
--   Kernel of a degree-one local bridge
-- statement:
--   Let $H$ and $D$ be groups and $\pi : H \to D$ a surjective homomorphism. Let $R, P, B$ be $\mathbb{Z}$-linear representations of $D$ and $f : R \to P$, $g : P \to B$ morphisms such that the underlying additive maps form an exact sequence and $g$ is surjective. Let $X$ be a $\mathbb{Z}$-linear representation of $D$ and $A$ one of $H$, and $\iota : X \to A$ an injective additive map with $\iota(\rho_X(\pi h)x) = \rho_A(h)\iota(x)$ for all $h, x$, such that every $a \in A$ fixed by all $s$ with $\pi s = 1$ lies in the image of $\iota$. Let $p$ be a natural number, $M$ a $\mathbb{Z}/p$-linear representation of $H$, and $\kappa : B \to \mathrm{Hom}(M, A)$ biadditive with $\kappa(\rho_B(\pi h)b)(\rho_M(h)m) = \rho_A(h)\kappa(b)(m)$ and such that every additive $c : B \to A$ is $\kappa(\cdot)(m)$ for a unique $m \in M$. Assume furthermore that every $D$-morphism $\varphi : R \to X$ admits an element $\psi$ of the internal hom from the restriction of $P$ along $\pi$ to $A$, in $H$-representations, with $\psi(f(x)) = \iota(\varphi(x))$ for all $x \in R$. Then for any additive $\Lambda$ from $D$-morphisms $R \to X$ to $H^1(H, M)$ satisfying the predicate `IsLocalBridge₁` for $\pi, f, g, \iota, \kappa$, and any $D$-morphism $\varphi : R \to X$, one has $\Lambda(\varphi) = 0$ if and only if $\varphi = \chi \circ f$ for some $D$-morphism $\chi : P \to X$.
--
--   This computes the kernel of a degree-one local bridge map: it is exactly the image of $\mathrm{Hom}_D(P, X)$ under restriction along $f$, so that $\mathrm{Ext}^1_D(B, X) = \mathrm{Hom}_D(R, X)/f^{*}\mathrm{Hom}_D(P, X)$ embeds into $H^1(H, M)$. It is used in the construction of such bridge maps at the archimedean places and at the $p$-adic places of a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isLocalBridge1_apply_eq_zero_iff.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_LocalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.isLocalBridge1_apply_eq_zero_iff
    {H : Type} [Group H] {D : Type} [Group D] (π : H →* D) (hπ : Function.Surjective π)
    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {X : Rep ℤ D} {A : Rep ℤ H} (ι : X →+ A) (hι : Function.Injective ι)
    (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
    (hιfix : ∀ a : A, (∀ s : H, π s = 1 → A.ρ s a = a) → ∃ x : X, ι x = a)
    {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)
    (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hdiv : ∀ φ : R ⟶ X, ∃ ψ : (ihom (Rep.res π P)).obj A, ∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ.hom x))
    {Λ : (R ⟶ X) →+ H1 M} (hΛ : IsLocalBridge₁ π f g ι κ Λ) (φ : R ⟶ X) :
    Λ φ = 0 ↔ ∃ χ : P ⟶ X, f ≫ χ = φ := by sorry
