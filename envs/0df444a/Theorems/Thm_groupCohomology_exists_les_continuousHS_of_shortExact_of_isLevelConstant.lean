-- Prove2me | Theorems.Thm_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant
-- name    : groupCohomology.exists_les_continuousHS_of_shortExact_of_isLevelConstant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/db44413e-ba9b-5df5-8d1f-a076f2e2bd5b
-- title:
--   Long exact sequence for S-ramified continuous cohomology in degrees 0,1,2
-- statement:
--   Let $p$ be a prime and $S$ a finite set of primes containing $p$ (as the element `pPrime p` of `Nat.Primes`). Let $N_1,N_2,N_3$ be finite-dimensional representations of the abstract group $G=\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$ over $\mathbf F_p=\mathbb{Z}/p$, and let $f:N_1\to N_2$, $g:N_2\to N_3$ be morphisms with $f$ followed by $g$ zero, such that the resulting short complex is short exact. Assume $N_2$ is smooth, i.e. each $m\in N_2$ is fixed by the fixing subgroup of some finite extension $F/\mathbf Q$ inside $\overline{\mathbf Q}$, and unramified outside $S$, i.e. for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbf Q}$ in which $q$ is a non-unit, every element of the image in $G$ of the inertia subgroup of $A$ over $\mathbf Q$ acts as the identity on $N_2$. The conclusion asserts the existence of $\mathbf F_p$-linear maps
--   $$N_1^{G}\xrightarrow{i_0}N_2^{G}\xrightarrow{p_0}N_3^{G}\xrightarrow{\delta_0}H^1_S(N_1)\xrightarrow{i_1}H^1_S(N_2)\xrightarrow{p_1}H^1_S(N_3)\xrightarrow{\delta_1}H^2_S(N_1)\xrightarrow{i_2}H^2_S(N_2)\xrightarrow{p_2}H^2_S(N_3),$$
--   where $N^{G}$ is the invariants submodule of the representation, $H^1_S(N)=$ `continuousH1S S N` is the image of `levelCocyclesS₁ S N` under the projection $H^1\pi$ to $H^1(G,N)$, and $H^2_S(N)=$ `continuousH2S S N` is the quotient of `levelCocyclesS₂ S N` by the elements of it lying in `levelCoboundariesS₂ S N`, together with the following pinning clauses and exactness. The maps $i_0,p_0$ are given on underlying elements by $f$ and $g$; $i_1,p_1$ are given on underlying $H^1$-classes by the maps induced by $f$ and $g$ on $H^1$ along the identity of $G$ (so in particular these induced maps carry $H^1_S$ into $H^1_S$). For $x\in N_3^{G}$, any $y\in N_2$ with $g(y)=x$ and any $1$-cocycle $c$ of $N_1$ with $f(c(s))=\rho_{N_2}(s)y-y$ for all $s$, one has $\delta_0 x=[c]$. For $z\in$ `levelCocyclesS₂ S N₁` and $z'\in$ `levelCocyclesS₂ S N₂` whose underlying functions on $G\times G$ satisfy $z'=f\circ z$, one has $i_2[z]=[z']$, and likewise $p_2$ is pinned by $z'=g\circ z$. For $x\in H^1_S(N_3)$, a $1$-cocycle $c$ of $N_3$ representing $x$, a function $b:G\to N_2$ with $g(b(s))=c(s)$ for all $s$ satisfying the predicate `IsLevelConstantS₁ S`, and $e\in$ `levelCocyclesS₂ S N₁` with $f(e(s,t))=\rho_{N_2}(s)(b(t))-b(st)+b(s)$ for all $s,t$, one has $\delta_1 x=[e]$. Finally $i_0$ is injective and the sequence is exact (image equals kernel) at the seven interior spots, i.e. at $N_2^G$, $N_3^G$, $H^1_S(N_1)$, $H^1_S(N_2)$, $H^1_S(N_3)$, $H^2_S(N_1)$ and $H^2_S(N_2)$. Surjectivity of $p_2$ is not asserted.
--
--   This is the long exact cohomology sequence, truncated in degrees $0$, $1$, $2$, for the $S$-ramified continuous cohomology of $\mathbf F_p$-representations of the absolute Galois group of $\mathbf Q$, with all eight maps pinned by explicit cochain formulas — the connecting map $\delta_1$ only on $S$-level-constant set-theoretic lifts. It supports the finiteness of $H^2_S$ ([`TWNum.finiteDimensional_continuousH2S`](thm.html#TWNum.finiteDimensional_continuousH2S)) and the additivity of the Euler defect in short exact sequences ([`groupCohomology.eulerDefect_add_of_shortExact_of_ne_two`](thm.html#groupCohomology.eulerDefect_add_of_shortExact_of_ne_two)), which feed the numerical estimates of the Taylor–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_les_continuousHS_of_shortExact_of_isLevelConstant
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (N1 N2 N3 : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) N1] [FiniteDimensional (ZMod p) N2] [FiniteDimensional (ZMod p) N3]
    (f : N1 ⟶ N2) (g : N2 ⟶ N3) (hfg : f ≫ g = 0)
    (hex : (ShortComplex.mk f g hfg).ShortExact)
    (hsm : ∀ m : N2, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N2.ρ s m = m)
    (hur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N2.ρ s = 1) :
    ∃ (i₀ : N1.ρ.invariants →ₗ[ZMod p] N2.ρ.invariants) (p₀ : N2.ρ.invariants →ₗ[ZMod p] N3.ρ.invariants)
      (δ₀ : N3.ρ.invariants →ₗ[ZMod p] ↥(continuousH1S S N1))
      (i₁ : ↥(continuousH1S S N1) →ₗ[ZMod p] ↥(continuousH1S S N2))
      (p₁ : ↥(continuousH1S S N2) →ₗ[ZMod p] ↥(continuousH1S S N3))
      (δ₁ : ↥(continuousH1S S N3) →ₗ[ZMod p] continuousH2S S N1)
      (i₂ : continuousH2S S N1 →ₗ[ZMod p] continuousH2S S N2)
      (p₂ : continuousH2S S N2 →ₗ[ZMod p] continuousH2S S N3),

      (∀ x, (i₀ x : N2) = f.hom x) ∧ (∀ y, (p₀ y : N3) = g.hom y) ∧
      (∀ x, (i₁ x : H1 N2) = (map (MonoidHom.id _) f 1).hom x) ∧
      (∀ y, (p₁ y : H1 N3) = (map (MonoidHom.id _) g 1).hom y) ∧

      (∀ (x : N3.ρ.invariants) (y : N2) (c : cocycles₁ N1), g.hom y = (x : N3) →
          (∀ s, f.hom (c s) = N2.ρ s y - y) → (δ₀ x : H1 N1) = (H1π N1).hom c) ∧

      (∀ (z : levelCocyclesS₂ S N1) (z' : levelCocyclesS₂ S N2),
          (∀ st, (z' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) st = f.hom ((z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N1) st)) → i₂ (continuousH2Sπ S N1 z) = continuousH2Sπ S N2 z') ∧
      (∀ (z : levelCocyclesS₂ S N2) (z' : levelCocyclesS₂ S N3),
          (∀ st, (z' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N3) st = g.hom ((z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) st)) → p₂ (continuousH2Sπ S N2 z) = continuousH2Sπ S N3 z') ∧

      (∀ (x : ↥(continuousH1S S N3)) (c : cocycles₁ N3) (b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) (e : levelCocyclesS₂ S N1),
          (H1π N3).hom c = (x : H1 N3) → (∀ s, g.hom (b s) = c s) → IsLevelConstantS₁ S b →
          (∀ s t, f.hom ((e : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N1) (s, t)) = N2.ρ s (b t) - b (s * t) + b s) →
          δ₁ x = continuousH2Sπ S N1 e) ∧

      Function.Injective i₀ ∧ Function.Exact i₀ p₀ ∧ Function.Exact p₀ δ₀ ∧ Function.Exact δ₀ i₁ ∧
      Function.Exact i₁ p₁ ∧ Function.Exact p₁ δ₁ ∧ Function.Exact δ₁ i₂ ∧ Function.Exact i₂ p₂ := by sorry
