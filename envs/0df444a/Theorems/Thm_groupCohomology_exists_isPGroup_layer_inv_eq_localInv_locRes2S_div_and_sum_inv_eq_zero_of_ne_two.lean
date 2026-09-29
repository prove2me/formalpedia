-- Prove2me | Theorems.Thm_groupCohomology_exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two
-- name    : groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5e8c07d4-c581-5630-a25e-eba843e71490
-- title:
--   Descent to a p-group layer and its local invariants, p odd
-- statement:
--   Fix a prime $p$ (as a `Fact`), a finite set $S$ of rational primes, and assume $p \neq 2$. Fix an element $\zeta$ of the algebraic closure of $\mathbb{Q}$ which is a primitive $p$-th root of unity, and let $c$ be an element of `continuousH2S S (ofChar (k := ZMod p) (cycloChar p))`, that is, of the quotient of the group `levelCocyclesS₂ S` of degree-$2$ cochains of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ at level $S$ by those degree-$2$ coboundaries which lie in it, with coefficients in the one-dimensional $\mathbb{Z}/p$-representation `ofChar (cycloChar p)`, i.e. the trivial representation twisted by the mod $p$ cyclotomic character $\chi_p$. The hypothesis `hc` asserts that the degree-$2$ restriction `locRes₂S` of $c$ along the archimedean local homomorphism `extArithLoc S (Sum.inl ())` vanishes.
--
--   Under these hypotheses there exist: number fields $E$ and $F$ with $F$ an $E$-algebra and $F/E$ Galois, such that $p \nmid [E:\mathbb{Q}]$ and $\mathrm{Gal}(F/E) = F \simeq_{\mathrm{alg}[E]} F$ is a $p$-group; idèle-theoretic descent data for $F/E$, namely a term $D$ of `IdeleGaloisDescent (𝓞 F) E F` (a homomorphism from $\mathrm{Gal}(F/E)$ to the ring automorphisms of the adèle ring of $F$, compatible with the structure map from $F$ and continuous), a multiplicative-distributive action of $\mathrm{Gal}(F/E)$ on the idèle class group $C_F = (\mathbb{A}_F)^\times / F^\times$ together with the assertion that this action agrees with `D.classAct`; a family $\iota_w : (F_w)^\times \to (\mathbb{A}_F)^\times$, indexed by the finite places $w$ of $F$ (height-one primes of $\mathcal{O}_F$), which concentrates a local unit at $w$: `finPart w (ι w x) = x`, `finPart w' (ι w x) = 1` for $w' \neq w$, and `infPart (ι w x) = 1`; a family of morphisms of representations $\mathrm{lam}_w$ from $(F_w)^\times$ with its $D_w$-action to the restriction along the inclusion of the decomposition group $D_w =$ [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82) of the $\mathrm{Gal}(F/E)$-module $C_F$, together with the assertion that $\mathrm{lam}_w$ sends a local unit $x$ to the class of $\iota_w(x)$ in $C_F$; a class $x \in H^2(\mathrm{Gal}(F/E), F^\times)$; a family of morphisms $\rho_w$ from the restriction to $D_w$ of $F^\times$ to $(F_w)^\times$, together with the assertion that $\rho_w$ is induced by the map $F^\times \to (F_w)^\times$ coming from $F \to F_w$; and a family $V$ assigning to each $q \in S$ the finite set of height-one primes $v$ of $\mathcal{O}_E$ with $q \in v$, characterised by that equivalence.
--
--   These data are such that the following holds for every pair of invariant systems $\mathrm{invG}$ and $\mathrm{inv}$, where $\mathrm{invG}$ is an additive homomorphism from $H^2(\mathrm{Gal}(F/E), C_F)$ to `AddCircle (1 : ℚ)` $= \mathbb{Q}/\mathbb{Z}$ and $\mathrm{inv}$ assigns to each subgroup $H \le \mathrm{Gal}(F/E)$ an additive homomorphism from $H^2(H, C_F)$ (coefficients restricted along the inclusion of $H$) to $\mathbb{Q}/\mathbb{Z}$, subject to the following groups of hypotheses. Injectivity: $\mathrm{invG}$ is injective, and so is $\mathrm{inv}\,H$ for every $H$. Image description: the range of $\mathrm{invG}$ consists exactly of the $t \in \mathbb{Q}/\mathbb{Z}$ with $\#\mathrm{Gal}(F/E)\cdot t = 0$, and the range of $\mathrm{inv}\,H$ of those $t$ with $\#H \cdot t = 0$. Restriction formula: for every $H$ and every class $x$ in $H^2(\mathrm{Gal}(F/E), C_F)$, the value of $\mathrm{inv}\,H$ on the restriction of $x$ to $H$ (the map induced by the inclusion of $H$ with the identity on coefficients) equals $[\,\mathrm{Gal}(F/E) : H\,] \cdot \mathrm{invG}(x)$. Local normalisation (one hypothesis with a long list of local data, summarised here): for every finite place $w$ of $F$, every prime $q$, every finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure carrying compatible $D_w$-actions on $L'$ and on $(L')^\times$ such that $D_w$ fixes the image of $\mathbb{Q}_q$ and the unit action is induced by the field action, every $D_w$-equivariant ring isomorphism $\Phi : F_w \cong L'$, every finite extension $K_0$ of $\mathbb{Q}_q$ with [`ExtCitation.LocalLevel.IsBase q L' D_w K₀`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13) (i.e. $K_0 \le L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D_w$), every morphism $\theta$ from $(L')^\times$ to $(F_w)^\times$ as $D_w$-modules which on units is given by $\Phi^{-1}$, and every class $u'$ in $H^2(D_w, (L')^\times)$ satisfying [`ExtCitation.LocalLevel.IsLocalFundamentalClass q L' D_w K₀ u'`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) (the predicate which, for all unramified overlayer data consisting of a larger finite extension $M \supseteq L'$ with a finite group $H$ acting faithfully, normal subgroups $N_L, N_n$, an isomorphism of $D_w$ with $H/N_L$, a Frobenius element $\varphi$ and a uniformiser $\pi$, pins down the image of $u'$ as the inflation of the class of the cocycle built from $\varphi$ and $\pi$): the value of $\mathrm{inv}\,D_w$ on the image of $u'$ under $\theta$ followed by $\mathrm{lam}_w$ equals the class of $1/\#D_w$ in $\mathbb{Q}/\mathbb{Z}$. Top-group compatibility: $\mathrm{invG}$ agrees with $\mathrm{inv}\,\top$ composed with restriction to the top subgroup.
--
--   For all such $\mathrm{invG}$ and $\mathrm{inv}$, the conclusion has two conjuncts.
--
--   (a) For every finite place $w$ of $F$ and every $q \in S$ with the image of $q$ lying in $w$, the value of $\mathrm{inv}\,D_w$ on the class obtained from $x$ by restricting to $D_w$, then pushing forward along $\rho_w$ and then along $\mathrm{lam}_w$, equals the class in $\mathbb{Q}/\mathbb{Z}$ of
--   $$\frac{e \cdot f \cdot a_q}{p},$$
--   where $v =$ `Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal` is the prime of $\mathcal{O}_E$ below $w$, $e =$ `Ideal.ramificationIdx'` and $f =$ `Ideal.inertiaDeg'` of $v$ over the ideal of $\mathbb{Z}$ generated by $q$, and $a_q =$ `ZMod.val` of `localInv p ζ q` applied to the degree-$2$ restriction `locRes₂S` of $c$ along `extArithLoc S (Sum.inr q)`, the local homomorphism at $q$; here `localInv p ζ q` is the $\mathbb{Z}/p$-linear functional on the continuous local $H^2$ singled out by the predicate `IsLocalInv p ζ q` when such a functional exists and is unique, and $0$ otherwise, and the product $e f a_q$ is taken as a natural number before being divided by $p$ in $\mathbb{Q}$.
--
--   (b) For every choice function $w$ assigning to $q \in S$ and a prime $v$ of $\mathcal{O}_E$ a finite place $w(q,v)$ of $F$, such that for all $q \in S$ and all $v \in V q$ the prime of $\mathcal{O}_E$ below $w(q,v)$ is $v$, the sum over $q \in S$ and over $v \in V q$ of the values of $\mathrm{inv}\,D_{w(q,v)}$ on the class obtained from $x$ by restriction to $D_{w(q,v)}$ followed by $\rho_{w(q,v)}$ and $\mathrm{lam}_{w(q,v)}$ vanishes in $\mathbb{Q}/\mathbb{Z}$.
--
--   This is the odd-$p$ form of the global descent step underlying the reciprocity law for local invariants: a class of the level-$S$ continuous $H^2$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with coefficients $\mathbb{F}_p(\chi_p)$, trivial at the archimedean place, is realised inside $H^2(\mathrm{Gal}(F/E), F^\times)$ for a Galois layer $F/E$ with $p$-group Galois group over a base of degree prime to $p$, in such a way that Tate's invariant maps compute its local contributions as $e f a_q / p$ and the sum of these contributions over all places above $S$ is zero. It is used by [`groupCohomology.sum_localInv_locRes2S_eq_zero_of_ne_two`](thm.html#groupCohomology.sum_localInv_locRes2S_eq_zero_of_ne_two), the statement that the sum of the local invariants of such a class vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (c : continuousH2S S (ofChar (k := ZMod p) (cycloChar p)))
    (hc : locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inl ())) c = 0) :
    ∃ (E F : Type) (_ : Field E) (_ : NumberField E) (_ : Field F) (_ : NumberField F) (_ : Algebra E F)
      (_ : IsGalois E F) (_ : ¬ p ∣ Module.finrank ℚ E)
    (_ : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    (_ : MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
    (_ : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))
    (ρ : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (u : Fˣ),
      (ρ w).hom (Additive.ofMul u) =
        Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))
    (V : ↥S → Finset (HeightOneSpectrum (𝓞 E)))
    (_ : ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 E)), v ∈ V q ↔ (((q : Nat.Primes) : ℕ) : 𝓞 E) ∈ v.asIdeal),
    ∀
    (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+
      AddCircle (1 : ℚ))
    (inv : ∀ H : Subgroup (F ≃ₐ[E] F),
      ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+
        AddCircle (1 : ℚ))

    (_ : Function.Injective invG)
    (_ : ∀ H : Subgroup (F ≃ₐ[E] F), Function.Injective (inv H))
    (_ : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0)
    (_ : ∀ (H : Subgroup (F ≃ₐ[E] F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0)

    (_ : ∀ (H : Subgroup (F ≃ₐ[E] F))
      (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
      inv H ((groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) =
          H.index • invG x)

    (_ : ∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L']
        [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]),
          g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ,
          ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))

    (_ : ∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
        invG x = inv ⊤ ((groupCohomology.map (⊤ : Subgroup (F ≃ₐ[E] F)).subtype
          (𝟙 (Rep.res (⊤ : Subgroup (F ≃ₐ[E] F)).subtype
            (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x)),

      (∀ (w : HeightOneSpectrum (𝓞 F)) (q : ↥S), (((q : Nat.Primes) : ℕ) : 𝓞 F) ∈ w.asIdeal →
          inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (ρ w) 2).hom
                ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
                  (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
                    (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom x))) =
          ((((Ideal.ramificationIdx' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
                (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
              Ideal.inertiaDeg' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
                (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
              ZMod.val
                (haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
                localInv p ζ (q : Nat.Primes)
                (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q)) c))
              : ℕ) : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))) ∧

      (∀ w : ↥S → HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 F),
        (∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 E)), v ∈ V q →
          Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) (w q v).asIdeal = v.asIdeal) →
        ∑ q : ↥S, ∑ v ∈ V q,
          inv (NumberField.PlaceDecomp.decomp E F (w q v))
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (w q v))) (lam (w q v)) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (w q v))) (ρ (w q v)) 2).hom
                ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F (w q v)).subtype
                  (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F (w q v)).subtype
                    (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom x))) = 0) := by sorry
