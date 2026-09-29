-- Prove2me | Theorems.Thm_groupCohomology_alpha1Read_comp_eq_sum_theta_of_forall_local
-- name    : groupCohomology.alpha1Read_comp_eq_sum_theta_of_forall_local
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/f072b35b-96a8-55c3-81b0-da92458f6057
-- title:
--   Global degree-one reading as a sum of local pairings
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes, and let $M$ be a representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $\mathbb{Z}/p$. Write $v$ for the elements of `extArithIndex S` $=\{*\}\sqcup S$ (an archimedean slot together with the primes of $S$), each equipped with its local group and homomorphism `extArithLoc S v` to the global Galois group, and $M^{\vee}(\chi)$ for the dual of $M$ twisted by the mod $p$ cyclotomic character `cycloChar p`. The data are: for each $v$ a $\mathbb{Z}/p$-linear map $\theta_v$ from the submodule `continuousH1` of classes of finite level in $H^1$ of the local restriction of $M$ to the dual of the corresponding submodule for $M^{\vee}(\chi)$; a hypothesis that every class in `continuousH1S S` of $M^{\vee}(\chi)$ has all its localisations `locTotal` lying in these submodules; a finite group $G$, subgroups $D_v$, representations $Y_v$ of $D_v$ over $\mathbb{Z}$, a representation $C$ of $G$, maps $\lambda_v\colon Y_v\to C|_{D_v}$, and $\lambda_J$ from $\prod_v \mathrm{Coind}_{D_v}^G Y_v$ to $C$ assumed equal to the sum over $v$ of the $v$-th projection followed by the adjoint of $\lambda_v$ under the coinduction–restriction adjunction; a finite representation $B$ over $\mathbb{Z}$ with $p\cdot b=0$ whose relation sequence `relationSeqInt B` is short exact and stays short exact after restriction to each $D_v$; invariant maps $\mathrm{inv}_G\colon H^2(G,C)\to\mathbb{Q}/\mathbb{Z}$ and $\mathrm{inv}_{D_v}\colon H^2(D_v,C|_{D_v})\to\mathbb{Q}/\mathbb{Z}$ compatible in the sense that $\mathrm{inv}_G\circ\mathrm{cor}=\mathrm{inv}_{D_v}$ for every additive $\mathrm{cor}$ with $\mathrm{cor}\circ\mathrm{res}$ equal to multiplication by $[G:D_v]$; an additive map $\mathrm{al}$ from $\mathrm{Hom}(R(B),C)$ to additive maps $H^1(G,B)\to\mathbb{Z}/p$ such that $\mathrm{inv}_G(\varphi_*\delta y)$ is the image of $\mathrm{al}(\varphi)(y)/p$ in $\mathbb{Q}/\mathbb{Z}$, $\delta$ being the connecting map of the relation sequence; an additive map $\mathrm{infl}\colon H^1(G,B)\to H^1(M^{\vee}(\chi))$; additive bridges $\Lambda_v$ from $\mathrm{Hom}_{D_v}(R(B)|_{D_v},Y_v)$ to `continuousH1` of the local restriction of $M$; units $u_v\in(\mathbb{Z}/p)^\times$; and the place-by-place hypothesis that for all $s_v\colon R(B)|_{D_v}\to Y_v$ and all $x\in H^1(G,B)$ with $\mathrm{infl}\,x\in$ `continuousH1S S` of $M^{\vee}(\chi)$, $\mathrm{inv}_{D_v}\bigl((s_v\cdot\lambda_v)_*\delta(\mathrm{res}\,x)\bigr)$ equals the image of $u_v\,\theta_v(\Lambda_v s_v)$ evaluated at the $v$-th localisation of $\mathrm{infl}\,x$, divided by $p$. The conclusion is that for every morphism $s\colon R(B)\to\prod_v\mathrm{Coind}_{D_v}^G Y_v$ and every $x\in H^1(G,B)$ with $\mathrm{infl}\,x$ in `continuousH1S S`, one has in $\mathbb{Z}/p$ the identity $\mathrm{al}(s\cdot\lambda_J)(x)=\sum_v u_v\,\theta_v\bigl(\Lambda_v s_v\bigr)$ applied to the $v$-th localisation of $\mathrm{infl}\,x$, where $s_v$ is the Frobenius-reciprocity transform of $s$ followed by the $v$-th projection.
--
--   This is the global-to-local assembly step in the duality computation underlying the Poitou–Tate style pairing: the invariant of the globally pushed-forward connecting class is the sum over the places in $\{\infty\}\cup S$ of the local Tate pairings, in the axiomatised form in which the surrounding development uses it. It is invoked in the construction of the nondegenerate pairing on the relevant Shafarevich–Tate groups and in the surjectivity statement for localisation maps on classes of finite level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_alpha1Read_comp_eq_sum_theta_of_forall_local.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation

theorem groupCohomology.alpha1Read_comp_eq_sum_theta_of_forall_local
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (θ : ∀ v : extArithIndex S,
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
    (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
      locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))

    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (D : extArithIndex S → Subgroup G) [∀ v, DecidableRel ⇑(QuotientGroup.rightRel (D v))]
    (Yv : ∀ v : extArithIndex S, Rep ℤ ↥(D v)) (C : Rep ℤ G)
    (lam : ∀ v, Yv v ⟶ Rep.res (D v).subtype C)
    (lamJ : GroupCohomology.RepPi.obj (fun v => Rep.coind (D v).subtype (Yv v)) ⟶ C)
    (hlamJ : lamJ = ∑ v, GroupCohomology.RepPi.proj (fun v => Rep.coind (D v).subtype (Yv v)) v ≫
      ((Rep.coindResAdjunction ℤ (D v)).homEquiv (Yv v) C).symm (lam v))

    (B : Rep ℤ G) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (hX : (Rep.relationSeqInt B).ShortExact)
    (hXv : ∀ v, ((Rep.relationSeqInt B).map (Rep.resFunctor (D v).subtype)).ShortExact)

    (invG : ↥(groupCohomology C 2) →+ AddCircle (1 : ℚ))
    (invD : ∀ v, ↥(groupCohomology (Rep.res (D v).subtype C) 2) →+ AddCircle (1 : ℚ))
    (hcor : ∀ (v : extArithIndex S) (cor : ↥(groupCohomology (Rep.res (D v).subtype C) 2) →+ ↥(groupCohomology C 2)),
      (∀ x : ↥(groupCohomology C 2), cor ((groupCohomology.map (D v).subtype (𝟙 (Rep.res (D v).subtype C)) 2).hom x) = (D v).index • x) →
      ∀ y, invG (cor y) = invD v y)

    (al : (Rep.relationModuleInt B ⟶ C) →+ (↥(groupCohomology B 1) →+ ZMod p))
    (hal : ∀ (φ : Rep.relationModuleInt B ⟶ C) (y : ↥(groupCohomology B 1)),
      invG ((groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y)) = ((((al φ y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (infl : ↥(groupCohomology B 1) →+ H1 (M.dualTwist (cycloChar p)))
    (Λ : ∀ v, (Rep.res (D v).subtype (Rep.relationModuleInt B) ⟶ Yv v) →+ ↥(continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)))
    (u : extArithIndex S → (ZMod p)ˣ)

    (hLOC : ∀ (v : extArithIndex S) (sv : Rep.res (D v).subtype (Rep.relationModuleInt B) ⟶ Yv v)
        (x : ↥(groupCohomology B 1)) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))),
      invD v ((groupCohomology.map (MonoidHom.id ↥(D v)) (sv ≫ lam v) 2).hom
        ((groupCohomology.δ (hXv v) 1 2 rfl).hom
          ((groupCohomology.map (D v).subtype (𝟙 (Rep.res (D v).subtype B)) 1).hom x)))
        = (((((u v : ZMod p) * θ v (Λ v sv) ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (s : Rep.relationModuleInt B ⟶ GroupCohomology.RepPi.obj (fun v => Rep.coind (D v).subtype (Yv v)))
    (x : ↥(groupCohomology B 1)) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))) :
    al (s ≫ lamJ) x = ∑ v, (u v : ZMod p) * θ v
      (Λ v (((Rep.resCoindAdjunction ℤ (D v).subtype).homEquiv (Rep.relationModuleInt B) (Yv v)).symm
        (s ≫ GroupCohomology.RepPi.proj (fun v => Rep.coind (D v).subtype (Yv v)) v)))
      ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩ := by sorry
