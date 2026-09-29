-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame
-- name    : groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/55cabddb-0d55-53c1-9a7a-39097825fa34
-- title:
--   Tame local Euler characteristic for subgroups of Gₚ
-- statement:
--   Let $p$ be a prime and let $q$ be a prime with $q = p$ as natural numbers, so that $\Gamma_q :=$ `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_p$-algebra automorphisms of the algebraic closure `PadicAlgCl` $p$ of $\mathbb{Q}_p$, is the absolute Galois group of $\mathbb{Q}_p$. Let $S \le \Gamma_q$ be a subgroup and let $N$ be a representation of $S$ on a finite-dimensional $\mathbb{Z}/p$-vector space. Assume there is a subgroup $S_0 \le S$ such that: (i) $S_0$ contains the preimage under `primeLocalToGlobal q` (the map $\Gamma_q \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to $\overline{\mathbb{Q}}$) of the fixing subgroup of some intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ of finite degree; (ii) $S_0 \cap S$, viewed as a subgroup of $S$, is normal in $S$; (iii) every $s \in S$ lying in $S_0$ acts trivially on $N$ and satisfies $\mathrm{cycloChar}\,p\,(\mathrm{primeLocalToGlobal}\,q\,s) = 1$, where $\mathrm{cycloChar}\,p$ is the mod $p$ cyclotomic character of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with values in $(\mathbb{Z}/p)^\times$; and (iv) $p$ does not divide the index of $S_0 \cap S$ in $S$. Then, writing $\chi$ for $\mathrm{cycloChar}\,p$ composed with `primeLocalToGlobal q` and with the inclusion $S \hookrightarrow \Gamma_q$, and $r$ for that inclusion followed by `primeLocalToGlobal q`, $$\dim_{\mathbb{Z}/p} \mathrm{continuousH1}\,r\,N = \dim_{\mathbb{Z}/p} N^{S} + \dim_{\mathbb{Z}/p} \bigl(N^{\vee}(\chi)\bigr)^{S} + [\Gamma_q : S]\cdot \dim_{\mathbb{Z}/p} N,$$ where $\mathrm{continuousH1}\,r\,N$ is the image in $H^1(S,N)$, under the canonical projection `H1π`, of the submodule `levelCocycles₁ r N` of $1$-cocycles, $N^{\vee}(\chi)$ is the dual representation of $N$ with $\rho$ replaced by $g \mapsto \chi(g)\cdot \rho^{\vee}(g)$, and $(-)^{S}$ denotes the invariants.
--
--   This is the tame case of the local Euler–Poincaré characteristic formula, in the form needed for an arbitrary subgroup $S$ of the absolute Galois group of $\mathbb{Q}_p$ satisfying the stated openness condition, the index $[\Gamma_q : S]$ playing the role of the degree $[K : \mathbb{Q}_p]$ of the corresponding finite level. It is obtained by transport from the same formula for $\mathrm{Gal}(\overline{\mathbb{Q}}_p/K)$ with $K$ of finite degree over $\mathbb{Q}_p$, and feeds the local dimension count [`groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal`](thm.html#groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal) used in the deformation-theoretic estimates at primes above $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p)
    (S : Subgroup (primeLocalGaloisGroup q)) (N : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) N]
    (htame : ∃ S₀ : Subgroup (primeLocalGaloisGroup q), S₀ ≤ S ∧
      (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
        F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S₀) ∧
      (S₀.subgroupOf S).Normal ∧
      (∀ s : S, (s : primeLocalGaloisGroup q) ∈ S₀ → N.ρ s = 1 ∧ cycloChar p (primeLocalToGlobal q s) = 1) ∧
      ¬ p ∣ (S₀.subgroupOf S).index) :
    Module.finrank (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) N)
      = Module.finrank (ZMod p) N.ρ.invariants
        + Module.finrank (ZMod p)
            (N.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants
        + S.index * Module.finrank (ZMod p) N := by sorry
