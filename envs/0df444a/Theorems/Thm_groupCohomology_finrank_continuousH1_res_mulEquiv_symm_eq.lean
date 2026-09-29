-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuousH1_res_mulEquiv_symm_eq
-- name    : groupCohomology.finrank_continuousH1_res_mulEquiv_symm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/84d9d116-2f3c-54bd-afbd-0995542e0d03
-- title:
--   Dimensions of invariants, twisted duals and continuous H¹ under group transport
-- statement:
--   Let $k$ be a field and let $G$, $G'$ be groups (all in one universe), let $e \colon G \simeq G'$ be a group isomorphism, let $r' \colon G' \to \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ be a homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, let $N$ be a $k$-linear representation of $G$, and let $\chi' \colon G' \to k^{\times}$ be a character. Write $N' =$ `Rep.res (e.symm) N` for the same $k$-module with $G'$ acting through $e^{-1}$. The assertion is a conjunction of three equalities of $k$-dimensions: first, $\dim_k (N')^{G'} = \dim_k N^{G}$; second, $\dim_k$ of the invariants of `(N').dualTwist χ'` equals $\dim_k$ of the invariants of `N.dualTwist (χ' ∘ e)`, where for a representation $A$ the object `A.dualTwist χ` is the linear dual $\operatorname{Dual}_k A$ with $g$ acting by $f \mapsto \chi(g)\,\bigl(f \circ A.\rho(g^{-1})\bigr)$; third, $\dim_k$ of `continuousH1 r' N'` equals $\dim_k$ of `continuousH1 (r' ∘ e) N`, where `continuousH1 r M` denotes the image in $H^1(\,\cdot\,, M)$, under the projection `H1π M`, of the submodule `levelCocycles₁ r M` of $1$-cocycles attached to the homomorphism $r$.
--
--   This is the dimension-counting form of transport of invariants, twisted-dual invariants and continuous $H^1$ along a group isomorphism compatible with the two maps to the absolute Galois group of $\mathbb{Q}$. It is used by [`groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame`](thm.html#groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame) in order to move a tame local $h^1$-count from an open subgroup to the absolute Galois group of its fixed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuousH1_res_mulEquiv_symm_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
universe u
open CategoryTheory groupCohomology

theorem groupCohomology.finrank_continuousH1_res_mulEquiv_symm_eq
    {k G G' : Type u} [Field k] [Group G] [Group G']
    (e : G ≃* G') (r' : G' →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (N : Rep.{u} k G) (χ' : G' →* kˣ) :
    Module.finrank k (Rep.res (e.symm : G' →* G) N).ρ.invariants = Module.finrank k N.ρ.invariants ∧
    Module.finrank k ((Rep.res (e.symm : G' →* G) N).dualTwist χ').ρ.invariants
      = Module.finrank k (N.dualTwist (χ'.comp (e : G →* G'))).ρ.invariants ∧
    Module.finrank k (groupCohomology.continuousH1 r' (Rep.res (e.symm : G' →* G) N))
      = Module.finrank k (groupCohomology.continuousH1 (r'.comp (e : G →* G')) N) := by sorry
