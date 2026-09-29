-- Prove2me | Theorems.Thm_groupCohomology_finrank_euler_coind_res_index_eq_mul
-- name    : groupCohomology.finrank_euler_coind_res_index_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/9df97d97-1086-5535-83fa-a6bbf339718e
-- title:
--   Euler characteristic of a coinduced module multiplies by p
-- statement:
--   Let $k$ be a field of characteristic $p$ with $p$ prime, let $G$ be a group, $r\colon G\to\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ a homomorphism into the automorphism group of `AlgebraicClosure ℚ` over $\mathbb Q$, and $S\le G$ a subgroup, so that $S$ acquires the homomorphism $r\circ\iota_S$ obtained by composing the inclusion $S\hookrightarrow G$ with $r$. Assume two standing hypotheses about $k$-linear representations of $S$: (HFIN) for every $M$ that is finite-dimensional over $k$ and smooth, in the sense that every $m\in M$ is fixed by all $s\in S$ with $(r\circ\iota_S)(s)$ in the fixing subgroup of some finite extension $F/\mathbb Q$ inside $\overline{\mathbb Q}$, both $\mathrm{continuousH1}$ of $M$ — the image in $H^1(S,M)$ of the submodule of level $1$-cocycles — and $\mathrm{continuousH2}$ of $M$ — the quotient of the level $2$-cocycles by those which are coboundaries — are finite-dimensional over $k$; and (HD2) for every morphism $\psi\colon B\to C$ of representations of $S$ with $B$ smooth and finite-dimensional and $\psi$ surjective on underlying modules, the induced map on $\mathrm{continuousH2}$ is surjective. Let $S''$ be a normal subgroup of $S$ which is open for $r\circ\iota_S$, i.e. contains the preimage under $r\circ\iota_S$ of the fixing subgroup of some finite extension $F_0/\mathbb Q$, and of index $p$ in $S$, and let $N$ be a smooth representation of $S$, finite-dimensional over $k$. Writing $I$ for the coinduction along $S''\hookrightarrow S$ of the restriction of $N$ to $S''$, the conclusion is the subtraction-free Euler-characteristic identity
--   $$\dim_k I^{S}+\dim_k \mathrm{continuousH2}(S,I)+p\,\dim_k \mathrm{continuousH1}(S,N)=\dim_k \mathrm{continuousH1}(S,I)+p\,\dim_k N^{S}+p\,\dim_k \mathrm{continuousH2}(S,N),$$
--   where invariants are taken for the respective $S$-actions and all continuous cohomology is formed with respect to $r\circ\iota_S$.
--
--   This is the index-$p$ step of the local Euler–Poincaré induction: it says that the Euler characteristic $\chi=h^0-h^1_{\mathrm{cts}}+h^2_{\mathrm{cts}}$ of the module coinduced from an open normal subgroup of index $p$ equals $p$ times that of the original module, stated without subtraction so as to avoid truncated natural-number arithmetic. It is used by [`groupCohomology.euler_poincare_identity_of_hypotheses`](thm.html#groupCohomology.euler_poincare_identity_of_hypotheses), and rests on the additivity of $\chi$ along short exact sequences with right-exact continuous $H^2$ together with the description of the coinduced module as the functions $S/S''\to N$ with the twisted diagonal action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_euler_coind_res_index_eq_mul.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.finrank_euler_coind_res_index_eq_mul {k G : Type u} [Field k] [Group G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (HFIN : ∀ (M : Rep.{u} k S), (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m) → FiniteDimensional k M →
        FiniteDimensional k (groupCohomology.continuousH1 (r.comp S.subtype) M) ∧
          FiniteDimensional k (groupCohomology.continuousH2 (r.comp S.subtype) M))
    (HD2 : ∀ (B C : Rep.{u} k S) (ψ : B ⟶ C), (∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
          FiniteDimensional ℚ F ∧ ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s m = m) → FiniteDimensional k B →
        Function.Surjective ψ.hom → Function.Surjective (groupCohomology.continuousH2MapHom (r.comp S.subtype) ψ))
    (S'' : Subgroup S) [S''.Normal]
    (hS'' : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (r.comp S.subtype) ≤ S'')
    (hidx : S''.index = p) (N : Rep.{u} k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) [FiniteDimensional k N] :
    Module.finrank k (Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ.invariants
      + Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) (Rep.coind S''.subtype (Rep.res S''.subtype N)))
      + p * Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) N)
    = Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) (Rep.coind S''.subtype (Rep.res S''.subtype N)))
      + p * Module.finrank k N.ρ.invariants
      + p * Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) N) := by sorry
