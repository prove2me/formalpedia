-- Prove2me | Theorems.Thm_groupCohomology_kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible
-- name    : groupCohomology.kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5afed680-a8dc-5172-9696-5f9a0fc1eb2f
-- title:
--   Kummer exactness in degrees 2–3 for S-level cohomology
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes, a group $G$ together with a homomorphism $r : G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, and a $\mathbb{Z}$-linear representation $E$ of $G$. Assume that for each $a \in E$ the orbit map $g \mapsto \rho_E(g)a$ satisfies the degree-one level condition `IsLevelConstantSr₁ r S`, and that $E$ is $p$-divisible: every $x \in E$ is $p\cdot y$ for some $y$. Call a function $b$ on $(\mathrm{Fin}\,n \to G)$ *of $S$-level* when there is an intermediate field $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ which is finite over $\mathbb{Q}$ and satisfies, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, that the inertia subgroup of $A$ over $\mathbb{Q}$ (viewed inside the Galois group) lies in the fixing subgroup of $F$, and such that $b(g \cdot s) = b(g)$ whenever $r(s_i)$ fixes $F$ pointwise for all $i$. Write $E[p]$ for `repTorsionP p E`, the representation of $G$ on the $p$-torsion submodule of $E$ over $\mathbb{Z}/p$, and let `continuousH2Sr r S E` be the quotient of the submodule `levelCocyclesSr₂ r S E` of $E$-valued cochains on $G \times G$ by the coboundaries it contains, with projection `continuousH2Srπ r S E`. Three assertions are made. First, every $c \in$ `levelCocyclesSr₂ r S E` admits a $b$ of $S$-level with $p \cdot b(v) = c(v_0,v_1)$ for all $v : \mathrm{Fin}\,2 \to G$. Secondly, for such a pair $(c,b)$, the cochain $d^{2,3}b$ agrees with $d^{2,3}$ of (the image in $E$ of) some $E[p]$-valued $2$-cochain $e$ of $S$-level if and only if the class `continuousH2Srπ r S E c` lies in $p \cdot$ `continuousH2Sr r S E`. Thirdly, for every $E[p]$-valued $3$-cochain $u$ of $S$-level with $d^{3,4}u = 0$ in the inhomogeneous cochain complex of $E[p]$, the cochain $u$ read in $E$ is $d^{2,3}w$ for some $E$-valued $2$-cochain $w$ of $S$-level if and only if there are $c \in$ `levelCocyclesSr₂ r S E`, an $E$-valued $b$ and an $E[p]$-valued $e$, both of $S$-level for one common field $F$ as above, with $p \cdot b(v) = c(v_0,v_1)$ for all $v$ and $u = d^{2,3}b + d^{2,3}e$ in $E$-valued cochains.
--
--   This is the degree-$2$/degree-$3$ portion of the Kummer (multiplication-by-$p$) long exact sequence for the unramified-outside-$S$, level-constant variant of group cohomology: exactness of $H^2_S(G,E) \xrightarrow{p} H^2_S(G,E) \xrightarrow{\delta} H^3_S(G,E[p]) \to H^3_S(G,E)$, spelt out in raw inhomogeneous cochains since no carrier for degree $3$ is introduced. It is used in the construction of level-constant $2$-cochains with trivial degree-$3$ differential under a condition on the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem groupCohomology.kummer_degreeThree_exactness_continuousH2Sr_of_smooth_of_divisible
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (E : Rep.{0} ℤ G)
    (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
    (hdiv : ∀ x : E, ∃ y : E, (p : ℤ) • y = x) :
    (∀ c : ↥(levelCocyclesSr₂ r S E), ∃ b : (Fin 2 → G) → E,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g) ∧
      ∀ v : Fin 2 → G, (p : ℤ) • b v = (c : G × G → E) (v 0, v 1)) ∧
    (∀ (c : ↥(levelCocyclesSr₂ r S E)) (b : (Fin 2 → G) → E),
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g) →
      (∀ v : Fin 2 → G, (p : ℤ) • b v = (c : G × G → E) (v 0, v 1)) →
      ((∃ e : (Fin 2 → G) → repTorsionP p E,
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
            ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → e (g * s) = e g) ∧
          ((inhomogeneousCochains E).d 2 3).hom b = ((inhomogeneousCochains E).d 2 3).hom (fun v => ((e v : repTorsionP p E) : E))) ↔
        ∃ y : continuousH2Sr r S E, continuousH2Srπ r S E c = p • y)) ∧
    (∀ u : (Fin 3 → G) → repTorsionP p E,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 3 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → u (g * s) = u g) →
      ((inhomogeneousCochains (repTorsionP p E)).d 3 4).hom u = 0 →
      ((∃ w : (Fin 2 → G) → E,
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
            ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
          ((inhomogeneousCochains E).d 2 3).hom w = fun t => ((u t : repTorsionP p E) : E)) ↔
        ∃ (c : ↥(levelCocyclesSr₂ r S E)) (b : (Fin 2 → G) → E) (e : (Fin 2 → G) → repTorsionP p E),
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
            ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g ∧ e (g * s) = e g) ∧
          (∀ v : Fin 2 → G, (p : ℤ) • b v = (c : G × G → E) (v 0, v 1)) ∧
          (fun t => ((u t : repTorsionP p E) : E)) =
            ((inhomogeneousCochains E).d 2 3).hom b + ((inhomogeneousCochains E).d 2 3).hom (fun v => ((e v : repTorsionP p E) : E)))) := by sorry
