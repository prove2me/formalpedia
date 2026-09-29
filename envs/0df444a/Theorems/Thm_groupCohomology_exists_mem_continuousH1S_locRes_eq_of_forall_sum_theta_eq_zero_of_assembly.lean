-- Prove2me | Theorems.Thm_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_of_assembly
-- name    : groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_of_assembly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/676d0c9b-d2e3-57b3-9a45-5d5c32d973d1
-- title:
--   Assembly of Poitou–Tate exactness at P¹_S from level data
-- statement:
--   Fix an odd prime $p$ and a finite set $S$ of primes with $p \in S$, and let $M$ be a finite-dimensional $\mathbb{Z}/p$-representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ which is smooth (each $m \in M$ is fixed by the fixing subgroup of some finite subextension $F/\mathbb{Q}$ of $\overline{\mathbb{Q}}$) and unramified outside $S$ (for $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q \in A^{\mathrm{nonunits}}$, every element of the image of the inertia subgroup of $A$ acts trivially). Write $M' = M^{\vee}(1)$ for the dual of $M$ twisted by the mod $p$ cyclotomic character `cycloChar p`, and index places by `extArithIndex S` $= \mathrm{Unit} \sqcup S$, with `extArithLoc` the archimedean local-to-global map at $\mathrm{inl}\,()$ and the local-to-global map at $q$ at $\mathrm{inr}\,q$. Here $\theta$ is a family of $\mathbb{Z}/p$-linear maps from $\mathrm{continuousH1}$ at $v$ of $M$ (the image in $H^1$ of `levelCocycles₁`) to the dual of $\mathrm{continuousH1}$ at $v$ of $M'$; $h\theta$ asserts, for each $q \in S$, that $\theta(\mathrm{inr}\,q)$ satisfies `IsTheta1` for the evaluation pairing of $M$ with $M'$ into $\mathrm{ofChar}$ of the local cyclotomic character and for the invariant `localInv p ζ q` attached to a primitive $p$-th root of unity $\zeta$, i.e. it computes the cup product of level-constant cocycles followed by that invariant; $\mathrm{invInf}$ is an injective functional on the corresponding $\mathrm{continuousH2}$ at the archimedean place and $h\theta\mathrm{inf}$ is the same `IsTheta1` condition there. Given a family $z$ of local classes, it is assumed that $z$ is orthogonal to all local families coming from $\mathrm{continuousH1S}\,S\,M'$ (the image of `levelCocyclesS₁`) under $\sum_v \theta_v$, that localisations of classes in $\mathrm{continuousH1S}\,S$ of $M'$ and of $M$ land in the local $\mathrm{continuousH1}$, that each local $\mathrm{continuousH1}$ of $M$ is finite-dimensional, and the reciprocity identity $hREC$: $\sum_v \theta_v(z'_v)(w_v) = 0$ whenever $z', w$ are local families matching the localisations of classes in $\mathrm{continuousH1S}\,S\,M$ and $\mathrm{continuousH1S}\,S\,M'$. The abstract input consists of three levels. At the first: a group $G$, $\mathbb{Z}$-representations $R, J, C$ of $G$ with $\lambda_J : J \to C$, an abelian group $VB$, a surjection $LJ1$ from $\mathrm{Hom}(R,J)$ onto the product of the local $\mathrm{continuousH1}$ of $M$, a bi-additive $al$ on $\mathrm{Hom}(R,C) \times VB$ with values in $\mathbb{Z}/p$, an additive $\mathrm{infl} : VB \to H^1(M')$ whose image is exactly $\mathrm{continuousH1S}\,S\,M'$, units $u_v$, and the identity $al(\lambda_J \circ s)(x) = \sum_v u_v\,\theta_v((LJ1\,s)_v)(\mathrm{loc}_v\,\mathrm{infl}\,x)$ for $\mathrm{infl}\,x$ in $\mathrm{continuousH1S}\,S\,M'$. At the second: a group $G_1$ with representations $R_1, P_1, J_1, C_1$, maps $f_1 : R_1 \to P_1$ and $\lambda_{J_1} : J_1 \to C_1$, an abelian group $VB_1$ with pairing $al_1$, transition maps $iS_1, iC_1$ and a surjection $iB_1$ compatible with $\lambda_J, \lambda_{J_1}$ and with $al, al_1$, the dichotomy that for every $\varphi : R \to C$ either $iC_1\varphi$ factors through $f_1$ or $al_1(iC_1\varphi)$ is non-zero on some element of $VB_1$, and a map $LJ1_1$ compatible with $LJ1$ along $iS_1$. At the third: a group $G_2$ with representations $R_2, P_2, E_2, J_2$, maps $f_2 : R_2 \to P_2$, $iEJ_2 : E_2 \to J_2$ and $iS_2$, the passage that $\lambda_{J_1} \circ t = \chi \circ f_1$ forces $iS_2 t = iEJ_2 \circ e + \chi' \circ f_2$ for some $e, \chi'$, an additive $LE1_2 : \mathrm{Hom}(R_2,E_2) \to H^1(M)$ with values in $\mathrm{continuousH1S}\,S\,M$, and $LJ1_2$ satisfying: $LJ1_2(iEJ_2 \circ e)$ localises $LE1_2 e$ place by place, $LJ1_2$ kills everything factoring through $f_2$, and $LJ1_2 \circ iS_2 = LJ1_1$. The conclusion is that there exists $x \in \mathrm{continuousH1S}\,S\,M$ whose localisation at each place $v$ equals $z_v$ in $H^1$.
--
--   This is the global direction of exactness of the Poitou–Tate sequence at $P^1_S$: a family of local classes orthogonal to the localisations of the dual Selmer-type group $\mathrm{continuousH1S}\,S\,M'$ is globally realised. It is stated as a purely formal assembly of the degree-one duality data at three Galois $S$-levels together with the reciprocity identity, and is cited by [`groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two`](thm.html#groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two), where the arithmetic inputs are supplied.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_of_assembly.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_of_assembly
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (θ : ∀ v : extArithIndex S,
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
    (hθ : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ (Sum.inr q)))
    (invInf : continuousH2 (extArithLoc S (Sum.inl ()))
        (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inl ())))) →ₗ[ZMod p] ZMod p)
    (hinvInf : Function.Injective invInf)
    (hθinf : IsTheta1 (extArithLoc S (Sum.inl ()))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inl ())) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inl ()))))
        invInf (θ (Sum.inl ())))
    (z : ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    (horth : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)),
        ∀ w : ∀ v : extArithIndex S, continuousH1 (extArithLoc S v)
            (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))),
          (∀ v, (w v : H1 _) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) v).hom y) →
          ∑ v : extArithIndex S, θ v (z v) (w v) = 0)

    (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
      locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈
        continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
    (hlocM : ∀ x ∈ continuousH1S S M, ∀ v : extArithIndex S,
      locTotal (extArithLoc S) M x v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    [∀ v : extArithIndex S, FiniteDimensional (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))]
    (hREC : ∀ (x : H1 M) (_ : x ∈ continuousH1S S M)
        (y : H1 (M.dualTwist (cycloChar p))) (_ : y ∈ continuousH1S S (M.dualTwist (cycloChar p)))
        (z' : ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
        (w : ∀ v : extArithIndex S, continuousH1 (extArithLoc S v)
          (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
        (_ : ∀ v, (z' v : H1 _) = (locRes (extArithLoc S) M v).hom x)
        (_ : ∀ v, (w v : H1 _) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) v).hom y),
        ∑ v : extArithIndex S, θ v (z' v) (w v) = 0)

    {G : Type} [Group G] (R J C : Rep ℤ G) (lamJ : J ⟶ C)
    (VB : Type) [AddCommGroup VB]
    (LJ1 : (R ⟶ J) →+ ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    (hJ1 : Function.Surjective LJ1)
    (al : (R ⟶ C) →+ VB →+ ZMod p)
    (infl : VB →+ H1 (M.dualTwist (cycloChar p)))
    (hrange : ∀ y : H1 (M.dualTwist (cycloChar p)), y ∈ continuousH1S S (M.dualTwist (cycloChar p)) ↔ ∃ x, infl x = y)
    (u : extArithIndex S → (ZMod p)ˣ)
    (hID : ∀ (s : R ⟶ J) (x : VB) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))),
      al (s ≫ lamJ) x = ∑ v : extArithIndex S, (u v : ZMod p) *
        θ v (LJ1 s v) ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩)

    {G₁ : Type} [Group G₁] (R₁ P₁ : Rep ℤ G₁) (f₁ : R₁ ⟶ P₁) (J₁ C₁ : Rep ℤ G₁) (lamJ₁ : J₁ ⟶ C₁)
    (VB₁ : Type) [AddCommGroup VB₁] (al₁ : (R₁ ⟶ C₁) →+ VB₁ →+ ZMod p)
    (iS₁ : (R ⟶ J) →+ (R₁ ⟶ J₁)) (iC₁ : (R ⟶ C) →+ (R₁ ⟶ C₁)) (iB₁ : VB →+ VB₁) (hiB₁ : Function.Surjective iB₁)
    (hiSlam₁ : ∀ s : R ⟶ J, iC₁ (s ≫ lamJ) = iS₁ s ≫ lamJ₁)
    (hial₁ : ∀ (φ : R ⟶ C) (x : VB), al₁ (iC₁ φ) (iB₁ x) = al φ x)
    (hEXF : ∀ φ : R ⟶ C, (∃ χ : P₁ ⟶ C₁, iC₁ φ = f₁ ≫ χ) ∨ ∃ x : VB₁, al₁ (iC₁ φ) x ≠ 0)
    (LJ1₁ : (R₁ ⟶ J₁) →+ ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    (hLJi₁ : ∀ s : R ⟶ J, LJ1₁ (iS₁ s) = LJ1 s)

    {G₂ : Type} [Group G₂] (R₂ P₂ : Rep ℤ G₂) (f₂ : R₂ ⟶ P₂) (E₂ J₂ : Rep ℤ G₂) (iEJ₂ : E₂ ⟶ J₂)
    (iS₂ : (R₁ ⟶ J₁) →+ (R₂ ⟶ J₂))
    (hPIT : ∀ (t : R₁ ⟶ J₁) (χ : P₁ ⟶ C₁), t ≫ lamJ₁ = f₁ ≫ χ →
      ∃ (e : R₂ ⟶ E₂) (χ' : P₂ ⟶ J₂), iS₂ t = e ≫ iEJ₂ + f₂ ≫ χ')
    (LE1₂ : (R₂ ⟶ E₂) →+ H1 M) (hLE1₂ : ∀ e : R₂ ⟶ E₂, LE1₂ e ∈ continuousH1S S M)
    (LJ1₂ : (R₂ ⟶ J₂) →+ ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    (hsq₂ : ∀ (e : R₂ ⟶ E₂) (v : extArithIndex S),
      ((LJ1₂ (e ≫ iEJ₂) v : continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)) : H1 _) =
        (locRes (extArithLoc S) M v).hom (LE1₂ e))
    (hLJf₂ : ∀ χ' : P₂ ⟶ J₂, LJ1₂ (f₂ ≫ χ') = 0)
    (hLJi₂ : ∀ t : R₁ ⟶ J₁, LJ1₂ (iS₂ t) = LJ1₁ t) :
    ∃ x ∈ continuousH1S S M, ∀ v, (locRes (extArithLoc S) M v).hom x = (z v : H1 _) := by sorry
