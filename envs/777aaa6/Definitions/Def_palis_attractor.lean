-- Prove2me | Definitions.Def_palis_attractor
-- name    : palis_attractor
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T02:52:16.758971+00:00
-- url     : https://prove2.me/theorems/8c3f1172-ee84-489b-bdbe-c233e57be989
-- title:
--   Attractors and basins of maps and flows
-- statement:
--   Let $M$ be a topological space modelled on $\mathbb R^n$.
--
--   *Discrete time.* For a map $T:M\to M$ and $p\in M$, the **$\omega$-limit set** $\omega(p)$ is the set of accumulation points of $(T^k p)_{k\ge0}$, namely $\omega(p)=\bigcap_{N}\overline{\{T^kp: k\ge N\}}$. The **basin** of $\Lambda\subset M$ is $B(\Lambda)=\{p\in M:\omega(p)\subset\Lambda\}$. The set $\Lambda$ is **transitive** if there is $x\in\Lambda$ with $\overline{\{T^kx:k\ge0\}}=\Lambda$, and $\Lambda$ is an **attractor** of $T$ if
--
--   1. $T(\Lambda)=\Lambda$ (invariance),
--   2. $\Lambda$ is transitive,
--   3. $B(\Lambda)$ is not Lebesgue-null.
--
--   $T$ **has finitely many attractors covering almost all of $M$** if there are finitely many attractors $\Lambda_1,\dots,\Lambda_k$ of $T$ such that $M\setminus\bigcup_i B(\Lambda_i)$ is Lebesgue-null.
--
--   *Continuous time.* For a flow $\Phi:\mathbb R\times M\to M$ the same notions are defined with $\omega(p)$ the set of accumulation points of $\Phi_t(p)$ as $t\to+\infty$, invariance meaning $\Phi_t(\Lambda)=\Lambda$ for every $t\in\mathbb R$, and transitivity meaning $\overline{\{\Phi_t x:t\ge0\}}=\Lambda$ for some $x\in\Lambda$.
--
--   These are exactly the notions in the Definition of the source: an attractor is an invariant, transitive set whose basin $B(\Lambda)=\{p:\omega(p)\subset\Lambda\}$ has positive Lebesgue measure.
--
--   **Formalization Note** $\omega$-limits are Mathlib's `omegaLimit atTop`. Lebesgue-nullity is `PalisConjecture.IsLebesgueNull`. The finite family of attractors is a `Finset (Set M)`.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib
import Definitions.Def_palis_lebesgue_null

/-!
# Attractors and their basins (discrete and continuous time)

Following the definition in the source: a set `Λ ⊆ M` is an *attractor* if it is invariant,
transitive, and its basin `B(Λ) = {p ∈ M | ω(p) ⊆ Λ}` has positive Lebesgue measure.
-/

namespace PalisConjecture

open Filter

variable {M : Type*} [TopologicalSpace M]

/-! ### Discrete time: a map `T : M → M` -/

/-- The ω-limit set `ω(p)` of `p` under iteration of `T`. -/
def omegaLimitMap (T : M → M) (p : M) : Set M :=
  omegaLimit atTop (fun (k : ℕ) (x : M) => T^[k] x) {p}

/-- The basin of attraction `B(Λ) = {p ∈ M | ω(p) ⊆ Λ}`. -/
def basin (T : M → M) (Λ : Set M) : Set M :=
  {p | omegaLimitMap T p ⊆ Λ}

/-- `Λ` is transitive: some point `x ∈ Λ` has forward orbit `{T^k x | k ≥ 0}` dense in `Λ`
(the closure of the orbit equals `Λ`). -/
def IsTransitive (T : M → M) (Λ : Set M) : Prop :=
  ∃ x ∈ Λ, closure {y | ∃ k : ℕ, T^[k] x = y} = Λ

/-- `Λ` is an attractor of `T`: invariant (`T(Λ) = Λ`), transitive, and its basin is not
Lebesgue-null. -/
def IsAttractor (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (T : M → M) (Λ : Set M) : Prop :=
  T '' Λ = Λ ∧ IsTransitive T Λ ∧ ¬ IsLebesgueNull n (basin T Λ)

/-- `T` exhibits finitely many attractors whose basins cover Lebesgue-almost all of `M`. -/
def HasFiniteAttractorsCoveringAE (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (T : M → M) : Prop :=
  ∃ A : Finset (Set M), (∀ Λ ∈ A, IsAttractor n T Λ) ∧
    IsLebesgueNull n (⋃ Λ ∈ A, basin T Λ)ᶜ

/-! ### Continuous time: a flow `Φ : ℝ → M → M` -/

/-- The ω-limit set `ω(p)` of `p` under the flow `Φ` as `t → +∞`. -/
def omegaLimitFlow (Φ : ℝ → M → M) (p : M) : Set M :=
  omegaLimit atTop Φ {p}

/-- The basin `B(Λ) = {p ∈ M | ω(p) ⊆ Λ}` for the flow `Φ`. -/
def flowBasin (Φ : ℝ → M → M) (Λ : Set M) : Set M :=
  {p | omegaLimitFlow Φ p ⊆ Λ}

/-- `Λ` is transitive for the flow: some `x ∈ Λ` has forward orbit `{Φ t x | t ≥ 0}` dense
in `Λ`. -/
def IsFlowTransitive (Φ : ℝ → M → M) (Λ : Set M) : Prop :=
  ∃ x ∈ Λ, closure {y | ∃ t : ℝ, 0 ≤ t ∧ Φ t x = y} = Λ

/-- `Λ` is an attractor of the flow `Φ`: invariant (`Φ_t(Λ) = Λ` for all `t`), transitive,
and its basin is not Lebesgue-null. -/
def IsFlowAttractor (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (Φ : ℝ → M → M) (Λ : Set M) : Prop :=
  (∀ t : ℝ, Φ t '' Λ = Λ) ∧ IsFlowTransitive Φ Λ ∧ ¬ IsLebesgueNull n (flowBasin Φ Λ)

/-- The flow `Φ` exhibits finitely many attractors whose basins cover Lebesgue-almost
all of `M`. -/
def FlowHasFiniteAttractorsCoveringAE (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (Φ : ℝ → M → M) : Prop :=
  ∃ A : Finset (Set M), (∀ Λ ∈ A, IsFlowAttractor n Φ Λ) ∧
    IsLebesgueNull n (⋃ Λ ∈ A, flowBasin Φ Λ)ᶜ

end PalisConjecture


