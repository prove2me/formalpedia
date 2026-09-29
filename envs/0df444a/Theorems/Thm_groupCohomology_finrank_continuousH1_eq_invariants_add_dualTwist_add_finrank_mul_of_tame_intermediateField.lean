-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField
-- name    : groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5763699c-d3ba-579e-9277-a798ef68fc18
-- title:
--   Tame local Euler characteristic over a finite base K/ℚₚ
-- statement:
--   Let $p$ be a prime, let $K$ be an intermediate field of the algebraic closure `PadicAlgCl p` of $\mathbb{Q}_p$ that is finite-dimensional over $\mathbb{Q}_p$, and let $K_w$ be an intermediate field of `PadicAlgCl p` over $K$ that is finite-dimensional and Galois over $K$, with $p \nmid [K_w : K]$. Write $r$ for the homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}_p/K)$ to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by identifying $K$-automorphisms with the elements of `K.fixingSubgroup` inside $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ and then applying [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41), which restricts scalars to $\mathbb{Q}$ and restricts to the chosen copy of $\overline{\mathbb{Q}}$ in $\overline{\mathbb{Q}}_p$. Let $M$ be a representation of $\mathrm{Gal}(\overline{\mathbb{Q}}_p/K)$ on a finite-dimensional $\mathbb{Z}/p$-vector space such that every element of `Kw.fixingSubgroup` acts as the identity on $M$ and has trivial image under the mod-$p$ cyclotomic character `cycloChar p` composed with $r$. Then the $\mathbb{Z}/p$-dimension of `continuousH1 r M`, the image in $H^1(\mathrm{Gal}(\overline{\mathbb{Q}}_p/K), M)$ of the submodule `levelCocycles₁` of $1$-cocycles of finite level with respect to $r$, equals $\dim M^{\mathrm{Gal}(\overline{\mathbb{Q}}_p/K)} + \dim (M^{\vee}(1))^{\mathrm{Gal}(\overline{\mathbb{Q}}_p/K)} + [K:\mathbb{Q}_p]\cdot \dim M$, where $M^{\vee}(1)$ is `M.dualTwist` of the dual representation of $M$ by `cycloChar p` composed with $r$, i.e. $g$ acting by `cycloChar p (r g)` times the dual action.
--
--   This is Tate's local Euler–Poincaré characteristic formula for a finite-dimensional mod-$p$ representation in the tame case, formulated over an arbitrary finite base field $K/\mathbb{Q}_p$ and with $h^2$ already expressed as $h^0$ of the Tate-twisted dual. It serves as the tame input to the Euler-characteristic computation over open subgroups of $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$, being cited by [`groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame`](thm.html#groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField
    {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (Kw : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K Kw] [IsGalois K Kw]
    (htame : ¬ p ∣ Module.finrank K Kw)
    (M : Rep.{0} (ZMod p) (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) [FiniteDimensional (ZMod p) M]
    (htriv : ∀ s ∈ Kw.fixingSubgroup, M.ρ s = 1)
    (hχ : ∀ s ∈ Kw.fixingSubgroup,
      cycloChar p (localGaloisToGlobal p ((IntermediateField.fixingSubgroupEquiv K).symm s)) = 1) :
    Module.finrank (ZMod p) (continuousH1 ((localGaloisToGlobal p).comp ((K.fixingSubgroup.subtype).comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)) M)
      = Module.finrank (ZMod p) M.ρ.invariants
        + Module.finrank (ZMod p) (M.dualTwist ((cycloChar p).comp ((localGaloisToGlobal p).comp ((K.fixingSubgroup.subtype).comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)))).ρ.invariants
        + Module.finrank ℚ_[p] K * Module.finrank (ZMod p) M := by sorry
