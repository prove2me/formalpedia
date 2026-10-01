-- Prove2me | Definitions.Def_ExtendedSmale9_GeneralAlgorithm
-- name    : ExtendedSmale9_GeneralAlgorithm
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T13:45:57.41296+00:00
-- url     : https://prove2.me/theorems/c9ca0cfa-652a-458b-a67e-a3534513cbc1
-- title:
--   General algorithms and the strong breakdown epsilon (Def. 9.3, (9.5), Def. 9.17)
-- statement:
--   A **computational problem** consists of an input set $\Omega$, an evaluation family $\Lambda = \{\Lambda_j : \Omega\to\mathbb C\}_{j}$, a metric space $M$, and a (possibly multivalued) solution map $\Xi:\Omega\rightrightarrows M$.
--
--   A **general algorithm** (Definition 9.3) is a map $\Gamma:\Omega\to M\cup\{\mathrm{NH}\}$ together with, for every $\iota$, a set $\Lambda_\Gamma(\iota)$ of evaluations such that
--   1. $\Lambda_\Gamma(\iota)$ is nonempty, and finite whenever $\Gamma(\iota)\neq\mathrm{NH}$;
--   2. if $\Lambda_j(\iota')=\Lambda_j(\iota)$ for all $j\in\Lambda_\Gamma(\iota)$, then $\Gamma(\iota')=\Gamma(\iota)$;
--   3. under the same hypothesis, $\Lambda_\Gamma(\iota')=\Lambda_\Gamma(\iota)$.
--
--   The error is $\operatorname{dist}(\Gamma(\iota),\Xi(\iota)) = \inf_{\xi\in\Xi(\iota)} d(\Gamma(\iota),\xi)\in[0,\infty]$, where the distance from $\mathrm{NH}$ to any point is $\infty$ (display (9.5)).
--
--   The **strong breakdown epsilon** (Definition 9.17) is
--   $$\varepsilon_B^s = \sup\{\varepsilon\ge0 : \forall\,\Gamma\ \exists\,\iota\in\Omega,\ \operatorname{dist}(\Gamma(\iota),\Xi(\iota))>\varepsilon\}.$$
-- source:
--   A. Bastounis, A. C. Hansen, V. Vlačić, *The extended Smale's 9th problem — On computational barriers and paradoxes in estimation, regularisation, computer-assisted proofs, and learning* (preprint, 126 pp., version of 28 Jan 2021), §9.2 Definition 9.3 and display (9.5) (p. 21), §9.4 Definition 9.17 (p. 25).

import Mathlib

/-!
# General algorithms and the strong breakdown epsilon

Bastounis–Hansen–Vlačić, *The extended Smale's 9th problem*, §9.2 (Definition 9.3,
display (9.5)) and §9.4 (Definition 9.17).

A computational problem `{Ξ, Ω, M, Λ}` is encoded by
* an input type `Ω`,
* an index type `Idx` and an evaluation family `Λ : Idx → Ω → ℂ`
  (the evaluation set is `{Λ j | j : Idx}`),
* a metric space `M`, and a (multivalued) solution map `Ξ : Ω → Set M`.
-/

open scoped ENNReal

namespace ExtendedSmale9

/-- A general algorithm (Definition 9.3) for a computational problem with evaluation
family `Λ : Idx → Ω → ℂ` and output space `M`.  The output `none` stands for the
non-halting output `NH`; `queried ι` is the set of (indices of) evaluations
`Λ_Γ(ι) ⊆ Λ` used on input `ι`. -/
structure GeneralAlgorithm {Ω Idx : Type*} (Λ : Idx → Ω → ℂ) (M : Type*) where
  /-- The output `Γ(ι) ∈ M ∪ {NH}` (`none` = `NH`). -/
  run : Ω → Option M
  /-- The set of evaluations `Λ_Γ(ι)` read on input `ι`. -/
  queried : Ω → Set Idx
  /-- (i) `Λ_Γ(ι)` is nonempty. -/
  queried_nonempty : ∀ ι, (queried ι).Nonempty
  /-- (i) `Λ_Γ(ι)` is finite whenever `Γ(ι) ≠ NH`. -/
  queried_finite : ∀ ι, run ι ≠ none → (queried ι).Finite
  /-- (ii) the action of `Γ` on `ι` is determined by `{f(ι)}_{f ∈ Λ_Γ(ι)}`. -/
  run_eq_of_agree : ∀ ι ι', (∀ j ∈ queried ι, Λ j ι' = Λ j ι) → run ι' = run ι
  /-- (iii) inputs agreeing on `Λ_Γ(ι)` have the same set of read evaluations. -/
  queried_eq_of_agree : ∀ ι ι', (∀ j ∈ queried ι, Λ j ι' = Λ j ι) → queried ι' = queried ι

/-- The error `dist_M(Γ(ι), Ξ(ι)) = inf_{ξ ∈ Ξ(ι)} d_M(Γ(ι), ξ)`, with the extended metric
(9.5): the distance from `NH` to any point of `M` is `∞`.  The infimum over the empty set
is `∞`. -/
noncomputable def errDist {M : Type*} [PseudoEMetricSpace M] (o : Option M) (S : Set M) :
    ℝ≥0∞ :=
  match o with
  | none => ⊤
  | some x => ⨅ ξ ∈ S, edist x ξ

/-- The strong breakdown epsilon (Definition 9.17):
`ε_B^s = sup {ε ≥ 0 | ∀ general algorithms Γ, ∃ ι ∈ Ω, dist_M(Γ(ι), Ξ(ι)) > ε}`. -/
noncomputable def strongBreakdownEps {Ω Idx M : Type*} [PseudoEMetricSpace M]
    (Λ : Idx → Ω → ℂ) (Ξ : Ω → Set M) : ℝ≥0∞ :=
  sSup {ε : ℝ≥0∞ | ∀ Γ : GeneralAlgorithm Λ M, ∃ ι : Ω, ε < errDist (Γ.run ι) (Ξ ι)}

end ExtendedSmale9


