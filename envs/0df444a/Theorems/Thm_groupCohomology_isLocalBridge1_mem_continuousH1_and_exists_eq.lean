-- Prove2me | Theorems.Thm_groupCohomology_isLocalBridge1_mem_continuousH1_and_exists_eq
-- name    : groupCohomology.isLocalBridge1_mem_continuousH1_and_exists_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5a009200-146c-5c97-8867-54aff3b4e4fa
-- title:
--   Image of the degree-one local bridge is exactly H¹_{cts}
-- statement:
--   Let $H$ be a group equipped with a homomorphism $r$ to the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, let $D$ be a group and $\pi \colon H \to D$ a surjective homomorphism which is assumed to kill a level subgroup: there is an intermediate field $F$ of $\mathbb{Q} \subseteq \mathrm{AlgebraicClosure}\ \mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with $\pi s = 1$ whenever $r s$ lies in the fixing subgroup of $F$. Let $R, P, B$ be $\mathbb{Z}$-linear representations of $D$ and $f \colon R \to P$, $g \colon P \to B$ morphisms whose underlying maps form an exact sequence with $g$ surjective. Let $X$ be a representation of $D$ and $A$ one of $H$, and let $\iota \colon X \to A$ be an injective additive map with $\iota(X.\rho(\pi h)x) = A.\rho(h)\iota(x)$ and such that every $a \in A$ fixed by all $s$ with $\pi s = 1$ is of the form $\iota x$. For a natural number $p$ and a representation $M$ of $H$ over $\mathbb{Z}/p$, let $\kappa \colon B \to (M \to A)$ be a biadditive pairing with $\kappa(B.\rho(\pi h)b)(M.\rho(h)m) = A.\rho(h)\kappa(b)(m)$, which identifies $M$ with the additive maps $B \to A$: every additive $c \colon B \to A$ is $\kappa(\cdot)(m)$ for a unique $m \in M$. Assume further that for each morphism $\varphi \colon R \to X$ of representations of $D$ there is an element $\psi$ of the internal hom $(\mathrm{ihom}(\mathrm{Rep.res}\ \pi\ P)).\mathrm{obj}\ A$, i.e. an additive map $P \to A$ carrying the $H$-action, with $\psi(f x) = \iota(\varphi x)$ for all $x \in R$ and fixed at some finite level (there is a finite-dimensional intermediate field $F$ with $A.\rho(s)\psi(x) = \psi(x)$ for all $x \in P$ and all $s$ with $r s$ in the fixing subgroup of $F$); and assume a Hilbert-90-type hypothesis: every $1$-cocycle $u$ of $H$ with values in that internal hom satisfying `IsLevelConstant₁ r u` is the image under $\mathrm{d}_{01}$ of some $\chi$ that is fixed at a finite level in the same sense. Finally let $\Lambda$ be an additive map from the morphisms $R \to X$ of representations of $D$ to $H^1(H,M)$ satisfying the predicate `IsLocalBridge₁` for the data $\pi, f, g, \iota, \kappa$. The conclusion is that $\Lambda \varphi$ lies in $\mathrm{continuousH1}\ r\ M$, the image under the quotient map `H1π M` of the submodule `levelCocycles₁ r M` of $1$-cocycles, for every $\varphi$, and conversely that every element of $\mathrm{continuousH1}\ r\ M$ is of the form $\Lambda \varphi$; that is, the range of $\Lambda$ is exactly this submodule of $H^1(H,M)$.
--
--   This is the surjectivity-and-well-definedness statement for the degree-one local bridge: under a level-compatibility hypothesis on $\pi$, a level-bounded lifting hypothesis along $f$ and a Hilbert-90-type vanishing statement for level-constant cocycles, an abstract bridge map $\Lambda$ has image precisely the continuous (level-constant) part of $H^1(H,M)$. It is used in the construction of local bridges at the archimedean and $p$-adic places of a number field, [`NumberField.InfPlaceDecomp.exists_isLocalBridge1_archimedean`](thm.html#NumberField.InfPlaceDecomp.exists_isLocalBridge1_archimedean) and [`NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl`](thm.html#NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isLocalBridge1_mem_continuousH1_and_exists_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_LocalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.isLocalBridge1_mem_continuousH1_and_exists_eq
    {H : Type} [Group H] (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {D : Type} [Group D] (π : H →* D) (hπ : Function.Surjective π)
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {X : Rep ℤ D} {A : Rep ℤ H} (ι : X →+ A) (hι : Function.Injective ι)
    (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
    (hιfix : ∀ a : A, (∀ s : H, π s = 1 → A.ρ s a = a) → ∃ x : X, ι x = a)
    {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)
    (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hdiv : ∀ φ : R ⟶ X, ∃ ψ : (ihom (Rep.res π P)).obj A,
      (∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ.hom x)) ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom ψ x) = LinearMap.toAddMonoidHom ψ x)
    (h90 : ∀ u : cocycles₁ ((ihom (Rep.res π P)).obj A), IsLevelConstant₁ r (u : H → (ihom (Rep.res π P)).obj A) →
      ∃ χ : (ihom (Rep.res π P)).obj A,
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x) ∧
        (d₀₁ ((ihom (Rep.res π P)).obj A)).hom χ = (u : H → (ihom (Rep.res π P)).obj A))
    {Λ : (R ⟶ X) →+ H1 M} (hΛ : IsLocalBridge₁ π f g ι κ Λ) :
    (∀ φ : R ⟶ X, Λ φ ∈ continuousH1 r M) ∧ (∀ y ∈ continuousH1 r M, ∃ φ : R ⟶ X, Λ φ = y) := by sorry
