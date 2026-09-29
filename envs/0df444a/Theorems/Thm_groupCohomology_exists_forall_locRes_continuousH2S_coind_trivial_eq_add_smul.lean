-- Prove2me | Theorems.Thm_groupCohomology_exists_forall_locRes_continuousH2S_coind_trivial_eq_add_smul
-- name    : groupCohomology.exists_forall_locRes_continuousH2S_coind_trivial_eq_add_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/8d264bff-87ba-550e-9da1-2f59de37f397
-- title:
--   Degree-two localisation for coinduced modules: cokernel of rank one
-- statement:
--   Let $p$ be a prime and $S$ a finite set of rational primes with $p \in S$, and let $F$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ that is Galois over $\mathbb{Q}$ and satisfies `IsUnramifiedOutside S`, i.e. $F$ is finite over $\mathbb{Q}$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $F$; assume further that if $p = 2$ then $F$ contains an element $i$ with $i^2 = -1$, and that the mod-$p$ cyclotomic character `cycloChar p` is trivial on the fixing subgroup $U$ of $F$. Write $P = \mathrm{CoInd}$ of the trivial one-dimensional $\mathbb{Z}/p$-representation of $U$ along the inclusion $U \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$. For $q \in S$ let $P_q$ be the restriction of $P$ along `extArithLoc S (Sum.inr q)`, the map from the local Galois group at $q$ into $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, and let $H^2_q$ be the corresponding degree-two continuous cohomology, namely `levelCocycles₂` modulo the `levelCoboundaries₂` it contains. The assertion is that there is a single family $w = (w_q)_{q \in S}$ of classes $w_q \in H^2_q$ such that every family $z = (z_q)_{q\in S}$ is of the form $z_q = \mathrm{loc}_q(x) + c \cdot w_q$ for all $q \in S$, for some class $x$ in the $S$-level global group `continuousH2S S P` and some scalar $c \in \mathbb{Z}/p$, where $\mathrm{loc}_q$ is the degree-two localisation map `locRes₂S` at $q$.
--
--   This is the rank-one coinduced case of the existence half of the Poitou–Tate exact sequence in degree two: the product of the local degree-two cohomologies at the primes of $S$ is spanned by the image of the global $S$-level $H^2$ together with one further class, so the cokernel of localisation is at most one-dimensional. It feeds the statement [`groupCohomology.exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one`](thm.html#groupCohomology.exists_forall_locRes_continuousH2S_coind_eq_add_sum_of_exists_sq_eq_neg_one), where the coefficient module is allowed to be a coinduced module of higher rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_forall_locRes_continuousH2S_coind_trivial_eq_add_smul.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_forall_locRes_continuousH2S_coind_trivial_eq_add_smul
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)
    (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1)
    (hFζ : ∀ s ∈ F.fixingSubgroup, cycloChar p s = 1) :
    ∃ w : ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q))
        (Rep.res (extArithLoc S (Sum.inr q))
          (Rep.coind F.fixingSubgroup.subtype (Rep.trivial (ZMod p) ↥F.fixingSubgroup (ZMod p)))),
      ∀ z : ∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q))
            (Rep.coind F.fixingSubgroup.subtype (Rep.trivial (ZMod p) ↥F.fixingSubgroup (ZMod p)))),
        ∃ (x : continuousH2S S (Rep.coind F.fixingSubgroup.subtype (Rep.trivial (ZMod p) ↥F.fixingSubgroup (ZMod p))))
          (c : ZMod p),
          ∀ q : ↥S, z q = locRes₂S S (Rep.coind F.fixingSubgroup.subtype (Rep.trivial (ZMod p) ↥F.fixingSubgroup (ZMod p)))
            (extArithLoc S (Sum.inr q)) x + c • w q := by sorry
