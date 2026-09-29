-- Prove2me | Theorems.Thm_groupCohomology_exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one
-- name    : groupCohomology.exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/0f2094b7-a5f2-5033-a72f-25215eaa32a2
-- title:
--   Cokernel bound for degree-two localisation at coinduced trivial modules
-- statement:
--   Let $p$ be a prime, $S$ a finite set of primes containing $p$ itself (as the element `pPrime p` of `Nat.Primes`), and let $F$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ which is Galois over $\mathbb{Q}$ and satisfies `IsUnramifiedOutside S`: $F/\mathbb{Q}$ is finite and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup $U =$ `F.fixingSubgroup`. Assume further that if $p = 2$ then $F$ contains an element $i$ with $i^2 = -1$, and that the mod-$p$ cyclotomic character `cycloChar p` is trivial on $U$. Let $N$ be a finite-dimensional representation of $U$ over $\mathbb{Z}/p$ on which every $u \in U$ acts as the identity, and put $M = \mathrm{CoInd}_U^{\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})} N$, i.e. `Rep.coind F.fixingSubgroup.subtype N`. Then there are an $n \in \mathbb{N}$ and a family $w : \mathrm{Fin}\, n \to \prod_{q \in S} \mathrm{continuousH2}$ of $M$ restricted along `extArithLoc S (Sum.inr q)`, the map $\mathrm{primeLocalToGlobal}$ from the local Galois group at $q$, such that $n$ is at most the $\mathbb{Z}/p$-dimension of the invariants of the dual of $M$ twisted by `cycloChar p` (the representation $g \mapsto \mathrm{cycloChar}_p(g)\cdot M^\vee(g)$), and such that every family $z$ of local degree-two classes at the primes of $S$ can be written as $z_q = \mathrm{locRes}_{2,S}(x)_q + \sum_i c_i\, w_i(q)$ for some global class $x$ in `continuousH2S S M` whose localisation along `extArithLoc S (Sum.inl ())` (the inclusion of the archimedean decomposition group) vanishes, and some $c : \mathrm{Fin}\,n \to \mathbb{Z}/p$.
--
--   This is the existence (surjectivity) half of the degree-two Poitou–Tate sequence, in the form of a bound on the cokernel of the localisation map $H^2(G_S, M) \to \bigoplus_{q \in S} H^2(\mathbb{Q}_q, M)$ restricted to families with vanishing archimedean component, for modules coinduced from a trivially acted module of the group $\mathrm{Gal}(\overline{\mathbb{Q}}/F)$, the cokernel being controlled by the invariants of the Cartier dual. It is the input to the computation of the image of the global-to-local map in degree two used in the bound on Selmer cokernels for $p \neq 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)
    (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1)
    (hFζ : ∀ s ∈ F.fixingSubgroup, cycloChar p s = 1)
    (N : Rep (ZMod p) ↥F.fixingSubgroup) [FiniteDimensional (ZMod p) N] (hN : ∀ u : ↥F.fixingSubgroup, N.ρ u = 1) :
    ∃ (n : ℕ) (w : Fin n → ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q)) (Rep.coind F.fixingSubgroup.subtype N))),
      n ≤ Module.finrank (ZMod p) ((Rep.coind F.fixingSubgroup.subtype N).dualTwist (cycloChar p)).ρ.invariants ∧
      ∀ z : ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (Rep.coind F.fixingSubgroup.subtype N)),
        ∃ (x : continuousH2S S (Rep.coind F.fixingSubgroup.subtype N)) (c : Fin n → ZMod p),
          locRes₂S S (Rep.coind F.fixingSubgroup.subtype N) (extArithLoc S (Sum.inl ())) x = 0 ∧
          ∀ q : ↥S, z q = locRes₂S S (Rep.coind F.fixingSubgroup.subtype N) (extArithLoc S (Sum.inr q)) x
            + ∑ i, c i • w i q := by sorry
