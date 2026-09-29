-- Prove2me | Theorems.Thm_groupCohomology_exists_cocycles2_units_eq_pow_of_levelCocyclesS2_ofChar_cycloChar
-- name    : groupCohomology.exists_cocycles2_units_eq_pow_of_levelCocyclesS2_ofChar_cycloChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/d737bd9d-49b8-58d0-8715-52b82ae4c1bd
-- title:
--   Descent of a cyclotomic mod-p 2-cocycle to F^×
-- statement:
--   Let $p$ be a prime and $S$ a finite set of primes. Let $\zeta$ be an element of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` that is a primitive $p$-th root of unity, and let $f$ be a function on pairs of $\mathbb{Q}$-automorphisms of $\overline{\mathbb{Q}}$ with values in `ofChar (cycloChar p)`, the one-dimensional representation of $\Gamma = \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ on $\mathbb{Z}/p$ obtained by twisting the trivial representation by the mod-$p$ cyclotomic character $\chi_p =$ `cycloChar p`, so that $\sigma$ acts as multiplication by $\chi_p(\sigma) \in (\mathbb{Z}/p)^\times$. Assume $f$ lies in `levelCocyclesS₂ S (ofChar (cycloChar p))`. Let $F$ be a number field that is Galois over $\mathbb{Q}$, $e : F \to \overline{\mathbb{Q}}$ a $\mathbb{Q}$-algebra map, and $\zeta_F \in F^\times$ a unit with $e(\zeta_F) = \zeta$. Assume further that $f(g s, g' s') = f(g, g')$ for all $g, g', s, s' \in \Gamma$ with $s$ and $s'$ fixing $e(F)$ pointwise. The conclusion asserts the existence of a function $b$ on pairs of elements of $\mathrm{Gal}(F/\mathbb{Q})$ with values in `Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ` (the group $F^\times$ written additively, with its Galois action) such that, for all $g, h \in \mathrm{Gal}(F/\mathbb{Q})$ and all $\hat g, \hat h \in \Gamma$ with $\hat g \circ e = e \circ g$ and $\hat h \circ e = e \circ h$, one has $b(g,h) = \zeta_F^{\,n}$ with $n$ the representative in $\{0,\dots,p-1\}$ of $f(\hat g, \hat h) \in \mathbb{Z}/p$, and such that $b$ is an inhomogeneous $2$-cocycle for that representation.
--
--   This is the Kummer-theoretic passage from a $2$-cocycle valued in the mod-$p$ cyclotomic line $\mathbb{F}_p(\chi_p)$ for the absolute Galois group to a $2$-cocycle of $\mathrm{Gal}(F/\mathbb{Q})$ valued in $F^\times$, realised by the inclusion $\mu_p \subset F^\times$ determined by $\zeta_F$. It is used in the construction of the $p$-group layer in the dual Selmer argument, being cited by [`groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two`](thm.html#groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_cocycles2_units_eq_pow_of_levelCocyclesS2_ofChar_cycloChar.lean

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

theorem groupCohomology.exists_cocycles2_units_eq_pow_of_levelCocyclesS2_ofChar_cycloChar
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      (ofChar (k := ZMod p) (cycloChar p)))
    (hf : f ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p)))
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] (e : F →ₐ[ℚ] AlgebraicClosure ℚ)
    (ζF : Fˣ) (hζF : e (ζF : F) = ζ)
    (hconst : ∀ g g' s s' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ y : F, s (e y) = e y) → (∀ y : F, s' (e y) = e y) → f (g * s, g' * s') = f (g, g')) :
    ∃ b : (F ≃ₐ[ℚ] F) × (F ≃ₐ[ℚ] F) → Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ,
      (∀ (g h : F ≃ₐ[ℚ] F) (ĝ ĥ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ y : F, ĝ (e y) = e (g y)) → (∀ y : F, ĥ (e y) = e (h y)) →
          b (g, h) = Additive.ofMul (ζF ^ ((f (ĝ, ĥ) : ZMod p).val))) ∧
      b ∈ cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ) := by sorry
