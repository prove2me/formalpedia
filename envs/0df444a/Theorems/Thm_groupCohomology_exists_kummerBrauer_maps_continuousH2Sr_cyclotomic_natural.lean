-- Prove2me | Theorems.Thm_groupCohomology_exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural
-- name    : groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/0954a909-4678-587e-bbc0-4cb1f3813bfa
-- title:
--   Natural Kummer–Brauer exact sequence for H²_S with μₚ
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$ itself, and let $L$ be a finite-dimensional intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `L.IsUnramifiedOutside S`, i.e. $L/\mathbb{Q}$ is finite and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup $\Gamma_L$ of $L$; assume moreover that if $p = 2$ then $L$ contains a square root of $-1$. Write $E_S$ for the $\mathbb{Z}[\Gamma_L]$-module `sUnitsMaxRep S L` (the $\Gamma_L$-stable group `sUnitsMaxStable S L` of $S$-units inside $\overline{\mathbb{Q}}^\times$, written additively), and $\mu_p$ for the $\mathbb{Z}/p$-representation of $\Gamma_L$ on $\mathbb{Z}/p$ obtained by twisting the trivial one by the mod-$p$ cyclotomic character `cycloChar p` restricted to $\Gamma_L$. The level-$S$ cohomology groups used are `continuousH1Sr`, the image of the level-$S$ $1$-cocycles `levelCocyclesSr₁` in $H^1$, and `continuousH2Sr`, the quotient of the level-$S$ $2$-cocycles `levelCocyclesSr₂` by those which are coboundaries. The assertion is the existence of $\mathbb{Z}/p$-linear maps $$\iota : \mathrm{continuousH1Sr}(\Gamma_L, S, E_S)/p \longrightarrow \mathrm{continuousH2Sr}(\Gamma_L, S, \mu_p), \qquad \mathrm{inv} : \mathrm{continuousH2Sr}(\Gamma_L, S, \mu_p) \longrightarrow (\mathrm{placesOverPrimes}\ L\ S \to \mathbb{Z}/p),$$ where the source of $\iota$ is the quotient by $p \cdot \top$ and $\mathrm{placesOverPrimes}\ L\ S$ is the set of height-one primes $w$ of $\mathcal{O}_L$ containing some prime of $S$, such that: $\iota$ is injective; the range of $\iota$ equals the kernel of $\mathrm{inv}$; a function $f$ lies in the range of $\mathrm{inv}$ exactly when $\sum^{f}_{w} f(w) = 0$; and both maps are natural in the following action-free form. For every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every $\tau \in \mathrm{Aut}_{\mathbb{Q}}(L)$ with $\sigma(y) = \tau(y)$ for all $y \in L$: (i) if $w, w'$ are level-$S$ $2$-cocycles with values in $\mu_p$ such that $w'(s,t) = \mathrm{cycloChar}_p(\sigma) \cdot w(s',t')$ whenever $\sigma^{-1} s \sigma = s'$ and $\sigma^{-1} t \sigma = t'$ in $\Gamma_L$, then for all places $v, v'$ in $\mathrm{placesOverPrimes}\ L\ S$ satisfying $v'(\tau y) = v(y)$ for all $y \in L$ one has $\mathrm{inv}([w'])(v') = \mathrm{inv}([w])(v)$; and (ii) if $c, c'$ are level-$S$ $1$-cocycles with values in $E_S$ such that the unit underlying $c'(s)$ equals $\sigma \cdot$ (the unit underlying $c(s')$) whenever $\sigma^{-1} s \sigma = s'$, then there exist level-$S$ $2$-cocycles $w, w'$ with values in $\mu_p$ whose classes are $\iota$ of the classes of $c$ and of $c'$ respectively, and which satisfy the same $\sigma$-twisted relation $w'(s,t) = \mathrm{cycloChar}_p(\sigma) \cdot w(s',t')$ as in (i).
--
--   This is the exact sequence $0 \to H^1_S(L, E_S)/p \to H^2_S(L, \mu_p) \to \mathbb{F}_p[S_f(L)] \xrightarrow{\Sigma} \mathbb{F}_p \to 0$, combining Kummer theory for the $S$-units of the maximal $S$-ramified extension with the local-invariant description of the $p$-torsion of the $S$-ramified $H^2$, here equipped with equivariance under those elements of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ that preserve $L$, expressed through the conjugation relations $\sigma^{-1} s \sigma = s'$ on cocycles and through transport of places by valuations. It feeds the construction of the cyclotomic quotient of $H^2$ used in the level-lowering bound on $S$-ramified cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1) :
    ∃ (ι : (↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) ⧸ ((p : ℤ) • (⊤ : Submodule ℤ ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))))) →ₗ[ZMod p] (continuousH2Sr L.fixingSubgroup.subtype S ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))) (inv : (continuousH2Sr L.fixingSubgroup.subtype S ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype))) →ₗ[ZMod p] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p)),
      Function.Injective ι ∧ LinearMap.range ι = LinearMap.ker inv ∧ (∀ f, f ∈ LinearMap.range inv ↔ ∑ᶠ w, f w = 0) ∧
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L), (∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ)) →

        (∀ (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
          (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
            (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
              ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')) →
          ∀ (v v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))), (∀ y : ↥L, (v'.1).valuation ↥L (τ y) = (v.1).valuation ↥L y) →
            inv (continuousH2Srπ L.fixingSubgroup.subtype S _ w') v' = inv (continuousH2Srπ L.fixingSubgroup.subtype S _ w) v) ∧

        (∀ (c c' : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))),
          (∀ s s' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' →
            sUnitsMaxRep.val S L ((c'.1 : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) s) = σ • sUnitsMaxRep.val S L ((c.1 : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) s')) →
          ∃ w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype))),
            ι (Submodule.Quotient.mk ⟨(H1π (sUnitsMaxRep S L)).hom c.1, H1π_mem_continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L) c.2⟩) =
              continuousH2Srπ L.fixingSubgroup.subtype S _ w ∧
            ι (Submodule.Quotient.mk ⟨(H1π (sUnitsMaxRep S L)).hom c'.1, H1π_mem_continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L) c'.2⟩) =
              continuousH2Srπ L.fixingSubgroup.subtype S _ w' ∧
            ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
              (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
                ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')) := by sorry
