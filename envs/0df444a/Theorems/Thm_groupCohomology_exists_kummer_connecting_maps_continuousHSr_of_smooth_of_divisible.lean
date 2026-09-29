-- Prove2me | Theorems.Thm_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible
-- name    : groupCohomology.exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/05d759f7-a0bf-5294-92ab-e7d66cf730b6
-- title:
--   Kummer maps δ,ι on S-level cohomology
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes, a group $G$ in universe $0$ together with a homomorphism $r : G \to \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ (the automorphisms of `AlgebraicClosure ℚ` over $\mathbb{Q}$), and a $\mathbb{Z}$-linear representation $E$ of $G$. Assume that for every $a \in E$ the orbit map $g \mapsto \rho(g)a$ satisfies the predicate `IsLevelConstantSr₁ r S`, and that $E$ is $p$-divisible: every $x \in E$ is of the form $(p : \mathbb{Z}) \cdot y$. Write $H^1_S(E)$ for `continuousH1Sr r S E`, the submodule of $H^1(G,E)$ that is the image of the level cocycles `levelCocyclesSr₁ r S E` under `H1π`, and $H^2_S(M)$ for `continuousH2Sr r S M`, the quotient of `levelCocyclesSr₂ r S M` by those of its elements lying in `levelCoboundariesSr₂ r S M`; let $E[p]$ denote `repTorsionP p E`, the $p$-torsion submodule $\mathrm{torsionBy}_{\mathbb{Z}}(E, p)$ with its induced $\mathrm{ZMod}\ p$-linear $G$-action. The assertion is the existence of additive maps $\delta : H^1_S(E) \to H^2_S(E[p])$ and $\iota : H^2_S(E[p]) \to H^2_S(E)$ with: $\delta x = 0$ iff $x \in p\,H^1_S(E)$; $\iota v = 0$ iff $v$ lies in the image of $\delta$; $w$ lies in the image of $\iota$ iff $p\,w = 0$; for every level $2$-cocycle $z$ valued in $E[p]$, the function $(g,h) \mapsto z(g,h)$ read in $E$ is again a level $2$-cocycle and $\iota$ sends the class of $z$ to its class, the classes being taken by `continuousH2Srπ`; and for every level $1$-cocycle $c$ of $E$ and every $b : G \to E$ satisfying `IsLevelConstantSr₁ r S` with $p\,b(g) = c(g)$ for all $g$, there is a level $2$-cocycle $w$ valued in $E[p]$ whose values in $E$ are those of $(d^{1,2}_E)(b)$ and whose class is $\delta$ of the class of $c$ in $H^1_S(E)$.
--
--   This is the Kummer (multiplication-by-$p$) portion of the long exact cohomology sequence attached to $0 \to E[p] \to E \to E \to 0$, transported to the $S$-level cohomology groups $H^1_S$, $H^2_S$ cut out by the level conditions relative to $r$ and $S$, with the two maps pinned on explicit cocycle representatives and all multiplications by $p$ taken as $\mathbb{N}$-actions so that they may be transported to any spelling of $H^1_S/p$ and $H^2_S[p]$. It feeds the cyclotomic Kummer–Brauer assembly [`groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural`](thm.html#groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem groupCohomology.exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (E : Rep.{0} ℤ G)
    (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
    (hdiv : ∀ x : E, ∃ y : E, (p : ℤ) • y = x) :
    ∃ (δ : ↥(continuousH1Sr r S E) →+ continuousH2Sr r S (repTorsionP p E))
      (ι : continuousH2Sr r S (repTorsionP p E) →+ continuousH2Sr r S E),
      (∀ x : ↥(continuousH1Sr r S E), δ x = 0 ↔ ∃ y : ↥(continuousH1Sr r S E), x = p • y) ∧
      (∀ v : continuousH2Sr r S (repTorsionP p E), ι v = 0 ↔ ∃ x, δ x = v) ∧
      (∀ w : continuousH2Sr r S E, (∃ v, ι v = w) ↔ p • w = 0) ∧
      (∀ z : ↥(levelCocyclesSr₂ r S (repTorsionP p E)),
        ∃ hz : (fun x : G × G => ((z : G × G → repTorsionP p E) x).1) ∈ levelCocyclesSr₂ r S E,
          ι (continuousH2Srπ r S (repTorsionP p E) z) = continuousH2Srπ r S E ⟨_, hz⟩) ∧
      (∀ (c : ↥(levelCocyclesSr₁ r S E)) (b : G → E), IsLevelConstantSr₁ r S b → (∀ g, p • b g = (c.1 : G → E) g) →
        ∃ w : ↥(levelCocyclesSr₂ r S (repTorsionP p E)),
          (∀ x : G × G, ((w : G × G → repTorsionP p E) x).1 = (d₁₂ E).hom b x) ∧
          δ ⟨(H1π E).hom c.1, H1π_mem_continuousH1Sr r S E c.2⟩ = continuousH2Srπ r S (repTorsionP p E) w) := by sorry
