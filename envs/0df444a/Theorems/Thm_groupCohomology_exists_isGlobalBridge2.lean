-- Prove2me | Theorems.Thm_groupCohomology_exists_isGlobalBridge2
-- name    : groupCohomology.exists_isGlobalBridge2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/c173759c-82a3-536c-afa1-1285f989d1ac
-- title:
--   Existence of a global degree-two bridge map
-- statement:
--   Fix a finite set $S$ of rational primes and write $\Gamma = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ for the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. The data are: a finite group $D$ and a homomorphism $\pi \colon \Gamma \to D$ which is trivial on the fixing subgroup of some intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is unramified outside $S$, meaning $F/\mathbb{Q}$ is finite-dimensional and for every prime $q \notin S$ and every valuation subring $\mathcal{A}$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $\mathcal{A}$, the image in $\Gamma$ of the inertia subgroup of $\mathcal{A}$ over $\mathbb{Q}$ lies in the fixing subgroup of $F$; $\mathbb{Z}$-linear $D$-representations $R, P, B$ with morphisms $f \colon R \to P$ and $g \colon P \to B$ whose underlying additive maps form an exact sequence at $P$ with $g$ surjective; a $\mathbb{Z}$-linear $D$-representation $X$, a $\mathbb{Z}$-linear $\Gamma$-representation $A$, and an injective additive map $\iota \colon X \to A$ with $\iota(X.\rho(\pi h)x) = A.\rho(h)(\iota x)$ for all $h \in \Gamma$, $x \in X$; a natural number $p$, a $\mathbb{Z}/p$-linear $\Gamma$-representation $M$, and a biadditive pairing $\kappa \colon B \times M \to A$ satisfying $\kappa(B.\rho(\pi h)b, M.\rho(h)m) = A.\rho(h)\,\kappa(b,m)$ and such that every additive map $c \colon B \to A$ equals $\kappa(\,\cdot\,,m)$ for a unique $m \in M$. Assume furthermore a divisibility hypothesis: for each additive $\varphi \colon R \to X$ there is an element $\psi$ of the internal hom $\operatorname{Hom}(\operatorname{Res}_\pi P, A)$ of $\Gamma$-representations with $\psi(f x) = \iota(\varphi x)$ for all $x \in R$, and an intermediate field, again unramified outside $S$ in the above sense, whose fixing subgroup acts trivially on all values of $\psi$. Then there exists an additive homomorphism $\Lambda$ from $H^1$ of the $D$-representation $\operatorname{Hom}(R,X)$ to `continuousH2S S M`, the quotient of the subgroup `levelCocyclesS₂ S M` by the preimage in it of `levelCoboundariesS₂ S M`, such that the predicate `IsGlobalBridge₂ S π f g ι κ Λ` holds.
--
--   This is the global, $S$-ramified counterpart of the degree-two local existence statement in the Tate-duality part of the argument: it supplies a connecting map from $H^1(D, \operatorname{Hom}(R,X))$ into the $S$-level $H^2$ of $M$ satisfying the bridge axioms, with the intended application $D = \operatorname{Gal}(F/\mathbb{Q})$, $X$ a group of $S$-units and $A = \overline{\mathbb{Q}}^\times$. Its purpose is to guarantee that the compatibility and inflation statements formulated for an arbitrary map satisfying `IsGlobalBridge₂` are non-vacuous; it is used in the analysis of inflation of level maps and in the non-degeneracy of the Šafarevič–Tate pairing away from $p = 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isGlobalBridge2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_GlobalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_isGlobalBridge2
    (S : Finset Nat.Primes)
    {D : Type} [Group D] [Finite D] (π : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* D)
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → π s = 1)
    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {X : Rep ℤ D} {A : Rep ℤ (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (ι : X →+ A) (hι : Function.Injective ι)
    (hιeq : ∀ (h : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
    {p : ℕ} {M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (κ : B →+ M →+ A)
    (hκeq : ∀ (h : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hdiv : ∀ φ : R →+ X, ∃ ψ : (ihom (Rep.res π P)).obj A,
      (∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ x)) ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom ψ x) = LinearMap.toAddMonoidHom ψ x) :
    ∃ Λ : H1 ((ihom R).obj X) →+ continuousH2S S M, IsGlobalBridge₂ S π f g ι κ Λ := by sorry
