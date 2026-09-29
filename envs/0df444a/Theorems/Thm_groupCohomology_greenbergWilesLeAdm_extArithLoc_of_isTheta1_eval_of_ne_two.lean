-- Prove2me | Theorems.Thm_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two
-- name    : groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5d483600-5737-5900-bc3c-f334418904aa
-- title:
--   Greenberg–Wiles inequality for the arithmetic localisation family, odd p
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $S$ be a finite set of primes containing $p$ itself (as `pPrime p`), and let $M$ be a finite-dimensional $\mathbf{Z}/p$-representation of $\mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ such that every vector of $M$ is fixed by the fixing subgroup of some finite extension of $\mathbf{Q}$ inside $\overline{\mathbf{Q}}$, and such that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbf{Q}}$ with $q$ a nonunit of $A$, the image of $A$'s inertia subgroup over $\mathbf{Q}$ acts trivially. Write $M' = M^{\vee}$ twisted by the mod $p$ cyclotomic character. Let $\mathrm{adm} \subseteq H^1(M)$ and $\mathrm{adm}' \subseteq H^1(M')$ be the submodules characterised as the classes of locally constant $1$-cocycles $c$ which, at every prime $q \notin S$ and every valuation subring over $q$, restrict on inertia to $g \mapsto \rho(g)m - m$ for some vector $m$. The localisation family is `extArithLoc S`, indexed by $\mathrm{Unit} \oplus S$: the inclusion of the archimedean decomposition subgroup at the first slot, and the local-to-global map from the local Galois group of $q$ at $q \in S$. Assume $H^1$ of $M$ restricted along the archimedean slot is a subsingleton. Given, for each slot $v$, a $\mathbf{Z}/p$-bilinear pairing between $H^1$ of $M$ and of $M'$ restricted to $v$, and local conditions $L(v) \subseteq H^1(\mathrm{res}_v M)$ with $L(\mathrm{inr}\,q)$ contained in `continuousH1` (the image of the level cocycles) for each $q \in S$; assume furthermore, for each $q \in S$, a bijective linear functional $\mathrm{inv}_q$ on the continuous $H^2$ of the trivial representation twisted by the cyclotomic character composed with the localisation map, a bijective linear map $\theta_q$ from the continuous $H^1$ of $\mathrm{res}_q M$ to the $\mathbf{Z}/p$-dual of the continuous $H^1$ of $\mathrm{res}_q M'$ satisfying `IsTheta1` for the evaluation pairing $M \times M^{\vee}(\chi) \to \mathbf{Z}/p(\chi)$ and $\mathrm{inv}_q$ — that is, $\theta_q$ sends a pair of classes of level-constant cocycles $f$, $g$ to $\mathrm{inv}_q$ of the class of any level $2$-cocycle agreeing with the cup cochain of $f$ and $g$ — and assume the given pairing at $\mathrm{inr}\,q$ agrees with $\theta_q$ on continuous classes. Then `greenbergWilesLeAdm` holds for these data: $$\dim \mathrm{Sel}(L,\mathrm{adm}) + \dim (M')^{\Gamma} + \sum_v \dim (\mathrm{res}_v M)^{\Gamma_v} \le \dim \mathrm{Sel}(L^{\perp},\mathrm{adm}') + \dim M^{\Gamma} + \sum_v \dim L(v),$$ where the dual Selmer group is taken with respect to the annihilators of the $L(v)$ under the given pairings.
--
--   This is the Greenberg–Wiles formula, in the inequality form used in the Poitou–Tate bookkeeping, specialised to the localisation family consisting of the archimedean place together with the primes of $S$ and to pairings pinned at the finite places to the evaluation duality between $M$ and its cyclotomic twisted dual. It restricts the general statement to odd $p$, and feeds the computation of the Selmer group attached to the unramified local menu in [`groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc`](thm.html#groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two.lean

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_SelmerAdm
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (adm : Submodule (ZMod p) (H1 M))
    (hadm : ∀ x : H1 M, x ∈ adm ↔
      ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
        (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
        H1π M c = x)
    (adm' : Submodule (ZMod p) (H1 (M.dualTwist (cycloChar p))))
    (hadm' : ∀ x : H1 (M.dualTwist (cycloChar p)), x ∈ adm' ↔
      ∃ c : cocycles₁ (M.dualTwist (cycloChar p)), IsLocallyConstant ⇑c ∧
        (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → ∃ m : M.dualTwist (cycloChar p),
            ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = (M.dualTwist (cycloChar p)).ρ g m - m) ∧
        H1π (M.dualTwist (cycloChar p)) c = x)
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M)))
    (pairing : ∀ v : extArithIndex S,
      H1 (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        H1 (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))) →ₗ[ZMod p] ZMod p)
    (L : ∀ v, Submodule (ZMod p) (H1 (Rep.res (extArithLoc S v) M)))
    (hLcts : ∀ q : ↥S,
      L (Sum.inr q) ≤
        continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
    (inv : ∀ q : ↥S,
      continuousH2 (extArithLoc S (Sum.inr q))
          (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) →ₗ[ZMod p]
        ZMod p)
    (hinv : ∀ q : ↥S, Function.Bijective (inv q))
    (θ : ∀ q : ↥S,
      continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθ : ∀ q : ↥S,
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (inv q) (θ q))
    (hbijθ : ∀ q : ↥S, Function.Bijective (θ q))
    (hagree : ∀ q : ↥S,
      ∀ (x : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
        (y : continuousH1 (extArithLoc S (Sum.inr q))
              (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))),
        pairing (Sum.inr q) (x : H1 _) (y : H1 _) = θ q x y) :
    greenbergWilesLeAdm (extArithLoc S) M (M.dualTwist (cycloChar p)) pairing L adm adm' := by sorry
