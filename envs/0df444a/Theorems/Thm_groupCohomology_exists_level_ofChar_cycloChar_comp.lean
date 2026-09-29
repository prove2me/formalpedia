-- Prove2me | Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
-- name    : groupCohomology.exists_level_ofChar_cycloChar_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/2eccaf59-51c4-5e0e-8170-3fb3f05126c9
-- title:
--   Finite level for the mod-p cyclotomic line
-- statement:
--   Let $p$ be a prime, $G$ a group, and $r : G \to \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ a group homomorphism into the automorphism group of the algebraic closure `AlgebraicClosure ℚ` of $\mathbb{Q}$ as a $\mathbb{Q}$-algebra. Write $\chi = (\mathtt{cycloChar } p) \circ r : G \to (\mathbb{Z}/p)^{\times}$, where `cycloChar p` sends an automorphism $\sigma$ to its value under the mod-$p$ cyclotomic character, i.e. to the unit of $\mathbb{Z}/p$ by which $\sigma$ acts on the $p$-th roots of unity of $\overline{\mathbb{Q}}$. The representation $\mathtt{ofChar }\chi$ is the trivial one-dimensional representation of $G$ over $k = \mathbb{Z}/p$ twisted by $\chi$: its underlying module is $\mathbb{Z}/p$ and $s \in G$ acts as multiplication by the scalar $\chi(s) \in \mathbb{Z}/p$. Let $m$ be an element of this representation. Then there is an intermediate field $F$ of the extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ which is finite-dimensional over $\mathbb{Q}$ such that for every $s \in G$ with $r(s)$ in the fixing subgroup of $F$ (that is, $r(s)$ fixes $F$ pointwise), the action of $s$ on $m$ returns $m$.
--
--   This is the statement that the line $\mathbb{F}_p(\chi_p \circ r)$ on which $G$ acts through the mod-$p$ cyclotomic character is, vector by vector, fixed by the Galois elements of a finite level, the level being $\mathbb{Q}(\zeta_p)$. It discharges the finite-level (smoothness) hypothesis on the coefficient module in the local Euler-characteristic and dual-twist computations of the Selmer-group bookkeeping, and is cited by the duality and tameness results there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_level_ofChar_cycloChar_comp.lean

import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation

theorem groupCohomology.exists_level_ofChar_cycloChar_comp
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (m : ofChar (k := ZMod p) ((cycloChar p).comp r)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → (ofChar (k := ZMod p) ((cycloChar p).comp r)).ρ s m = m := by sorry
