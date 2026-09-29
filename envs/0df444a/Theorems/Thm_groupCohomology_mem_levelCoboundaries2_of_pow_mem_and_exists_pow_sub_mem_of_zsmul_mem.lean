-- Prove2me | Theorems.Thm_groupCohomology_mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem
-- name    : groupCohomology.mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/cff3bf77-143e-5c96-a9ae-f9af967bd6c9
-- title:
--   Degree-two Kummer theory for μₚ⊂ℚ̄^×
-- statement:
--   Fix a prime $p$ and a subgroup $D$ of the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, together with a unit $\zeta$ of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ that is a primitive $p$-th root of unity and is fixed by every $\sigma \in D$. Two coefficient systems for $D$ are used: the trivial representation `Rep.trivial (ZMod p) ↥D (ZMod p)`, and the restriction along the inclusion `D.subtype` of the representation `Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)` of the automorphism group on the units of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, written additively via `Additive`. For a function $z : D \times D \to \mathbb{Z}/p$ put $\zeta^z : (g,h) \mapsto \zeta^{(z(g,h)).\mathrm{val}}$, the power taken along the natural-number representative of the residue and transported into the additive copy of the unit group. For both coefficient systems, cocycles and coboundaries in degree two are taken in the sense of `levelCocycles₂` and `levelCoboundaries₂` relative to the map `D.subtype`. The assertion is the conjunction of: (1) if $z$ lies in `levelCocycles₂` for the trivial $\mathbb{Z}/p$-coefficients and $\zeta^z$ lies in `levelCoboundaries₂` for the unit-group coefficients, then $z$ lies in `levelCoboundaries₂` for the trivial coefficients; and (2) if $X : D \times D \to \mathrm{Additive}\,(\mathrm{AlgebraicClosure}\,\mathbb{Q})^\times$ lies in `levelCocycles₂` and $(p : \mathbb{Z}) \cdot X$ lies in `levelCoboundaries₂`, then there is $z$ in `levelCocycles₂` for the trivial $\mathbb{Z}/p$-coefficients with $X - \zeta^z$ in `levelCoboundaries₂`.
--
--   This is the degree-two part of the Kummer sequence $1 \to \mu_p \to \overline{\mathbb{Q}}^\times \to \overline{\mathbb{Q}}^\times \to 1$ in cocycle form: part (1) expresses injectivity and part (2) surjectivity onto the $p$-torsion of the map $[z] \mapsto [\zeta^z]$ from $H^2(D, \mathbb{Z}/p)$ to $H^2(D, \overline{\mathbb{Q}}^\times)$, for the degree-two cohomology computed by cocycles and coboundaries of the indicated level with respect to the inclusion of $D$. It feeds into [`groupCohomology.exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one`](thm.html#groupCohomology.exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one), where local classes are compared with classes coming from $\mathbb{Z}/p$-coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem
    {p : ℕ} [Fact p.Prime] (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ p) (hD : ∀ σ ∈ D, σ • ζ = ζ) :
    (∀ z : ↥D × ↥D → ZMod p, z ∈ levelCocycles₂ D.subtype (Rep.trivial (ZMod p) ↥D (ZMod p)) →
      (fun g => Additive.ofMul (ζ ^ (z g).val) : ↥D × ↥D → Additive (AlgebraicClosure ℚ)ˣ) ∈
        levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))) →
      z ∈ levelCoboundaries₂ D.subtype (Rep.trivial (ZMod p) ↥D (ZMod p))) ∧
    (∀ X : ↥D × ↥D → Additive (AlgebraicClosure ℚ)ˣ,
      X ∈ levelCocycles₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))) →
      (p : ℤ) • X ∈ levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))) →
      ∃ z : ↥D × ↥D → ZMod p, z ∈ levelCocycles₂ D.subtype (Rep.trivial (ZMod p) ↥D (ZMod p)) ∧
        X - (fun g => Additive.ofMul (ζ ^ (z g).val)) ∈
          levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) := by sorry
