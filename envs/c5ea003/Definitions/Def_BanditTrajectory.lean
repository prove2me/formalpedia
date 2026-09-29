-- Prove2me | Definitions.Def_BanditTrajectory
-- name    : BanditTrajectory
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-30T03:27:56.700506+00:00
-- url     : https://prove2.me/theorems/9c00ae0a-a320-44c7-8587-0bb33dab3cbd
-- statement:
--   The infinite-horizon canonical bandit model and the fixed-confidence best-arm identification framework (L&S §33.2): the law $\mathbb{P}_{\nu\pi}$ of the infinite interaction trajectory $(A_1,X_1),(A_2,X_2),\dots$ built from the one-round step kernels by the Ionescu–Tulcea theorem; the natural filtration $\mathcal{F}_t = \sigma(A_1,X_1,\dots,A_t,X_t)$ and its ($\mathbb{N}\cup\{\infty\}$-valued) stopping times; and soundness of a triple $(\pi,\tau,\psi)$ at confidence $\delta$ (Definition 33.4):
--
--   $$\mathbb{P}_{\nu\pi}(\tau<\infty \text{ and } \Delta_{\psi}(\nu)>0)\le\delta \quad\text{for all } \nu \text{ in the class}.$$
--
--   Finally, the characteristic time $c^*(\nu)$ (Eq. 33.4) is defined by
--
--   $$c^*(\nu)^{-1} = \sup_{\alpha\in\mathcal{P}_{k-1}} \inf_{\nu'\in\mathcal{E}_{alt}(\nu)} \sum_i \alpha_i D(\nu_i,\nu'_i),$$
--
--   where $\mathcal{E}_{alt}(\nu)$ are the class members whose optimal arms all differ from $\nu$'s.
-- source:
--   L&S §33.2, Definition 33.4 and Eq. (33.4), pp.406-407

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Stopping
import Mathlib.Data.Real.ENatENNReal
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Definitions.Def_BanditPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §33.2:
the infinite-horizon canonical bandit model, stopping times and the
fixed-confidence best-arm-identification (BAI) framework.

* `banditTrajMeasure ν π`: the law of the infinite interaction trajectory
  `(A_1, X_1), (A_2, X_2), …` of policy `π` in environment `ν`, obtained from the
  one-round step kernels of the finite-horizon canonical model via Mathlib's
  Ionescu–Tulcea theorem (`ProbabilityTheory.Kernel.trajMeasure`). Trajectory
  coordinate `t : ℕ` is round `t + 1`, so a `BanditHistory k n` is the prefix of
  the first `n` coordinates. Ionescu–Tulcea consumes step kernels on histories
  indexed by `Finset.Iic n`; `banditIicHistory` transports them to the
  `BanditHistory k (n+1) = Fin (n+1) → Fin k × ℝ` format of `banditStepKernel`
  (the identity re-indexing `⟨t, t ≤ n⟩ ↦ ⟨t, t < n+1⟩`).
* `banditFiltration k`: the natural filtration `𝓕_t = σ(A_1, X_1, …, A_t, X_t)`
  (`𝓕_0` trivial), as the pullbacks of the length-`t` prefix maps.
* `IsBanditStoppingTime τ`: `τ : trajectories → ℕ∞` is a stopping time of the
  natural filtration (Mathlib `IsStoppingTime`; the value `⊤` means "never stop",
  which Definition 33.4 explicitly allows).
* `IsSoundBAI δ π τ ψ 𝓔` (Definition 33.4): the learner `(π, τ, ψ)` is *sound* at
  confidence level `δ` for the class `𝓔` if for every `ν ∈ 𝓔`,
  `ℙ_{νπ}(τ < ∞ and Δ_{ψ}(ν) > 0) ≤ δ`.
* `baiComplexity ν 𝓔` (Eq. (33.4)): the characteristic time `c*(ν)`, defined by
  `c*(ν)⁻¹ = ⨆_{α ∈ 𝓟_{k-1}} ⨅_{ν' ∈ 𝓔_alt(ν)} ∑ i, α i * D(ν i, ν' i)` where
  `𝓔_alt(ν)` is the set of members of `𝓔` whose optimal-arm set is disjoint from
  `ν`'s. The inversion is `ℝ≥0∞` inversion, which matches the book's conventions
  exactly: the book sets `c*(ν) = ∞` when `c*(ν)⁻¹ = 0` (`= ENNReal 0⁻¹ = ∞`),
  and when `𝓔_alt(ν) = ∅` the inner infimum is `∞`, giving `c*(ν) = ∞⁻¹ = 0`
  (no alternative to rule out, the lower bound is vacuous).
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal

namespace BanditAlgorithm

/-- Transport of an Ionescu–Tulcea history `Π i : Finset.Iic n, Fin k × ℝ` (trajectory
coordinates `0, …, n`) to the canonical-model history `BanditHistory k (n + 1)`:
the identity re-indexing along `Fin (n + 1) ≃ Finset.Iic n`. -/
def banditIicHistory (k n : ℕ) (x : Π _i : Finset.Iic n, Fin k × ℝ) :
    BanditHistory k (n + 1) :=
  fun t ↦ x ⟨(t : ℕ), Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp t.isLt)⟩

lemma measurable_banditIicHistory {k n : ℕ} : Measurable (banditIicHistory k n) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

/-- The one-round step kernel of the canonical model, re-indexed to the
`Finset.Iic`-history format consumed by the Ionescu–Tulcea theorem: given
trajectory coordinates `0, …, n` (rounds `1, …, n + 1`), the law of round `n + 2`. -/
noncomputable def banditTrajKernel {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (n : ℕ) : Kernel (Π _i : Finset.Iic n, Fin k × ℝ) (Fin k × ℝ) :=
  (banditStepKernel ν π (n + 1)).comap (banditIicHistory k n) measurable_banditIicHistory

instance banditTrajKernel.instIsMarkovKernel {k : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (n : ℕ) : IsMarkovKernel (banditTrajKernel ν π n) := by
  unfold banditTrajKernel
  infer_instance

/-- The infinite-horizon canonical bandit probability measure (L&S §4.6 extended to
§33.2's setting): the law `ℙ_{νπ}` of the infinite interaction trajectory
`(A_1, X_1), (A_2, X_2), …` (coordinate `t` is round `t + 1`) of the interconnection
of policy `π` and environment `ν`, built by the Ionescu–Tulcea theorem from the
initial round's law and the one-round step kernels. -/
noncomputable def banditTrajMeasure {k : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) : Measure (ℕ → Fin k × ℝ) :=
  Kernel.trajMeasure (X := fun _ ↦ Fin k × ℝ)
    (banditStepKernel ν π 0 fun t ↦ t.elim0) (banditTrajKernel ν π)

instance banditTrajMeasure.instIsProbabilityMeasure {k : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) : IsProbabilityMeasure (banditTrajMeasure ν π) := by
  unfold banditTrajMeasure
  infer_instance

/-- The prefix map returning the first `n` rounds of an infinite trajectory. -/
def banditTrajPrefix (k n : ℕ) (ω : ℕ → Fin k × ℝ) : BanditHistory k n :=
  fun t ↦ ω t

lemma measurable_banditTrajPrefix {k n : ℕ} : Measurable (banditTrajPrefix k n) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

/-- The natural filtration `𝔽 = (𝓕_t)_{t=0}^∞` of the bandit trajectory space
(L&S §33.2): `𝓕_t = σ(A_1, X_1, …, A_t, X_t)` is generated by the first `t` rounds;
`𝓕_0` is trivial. -/
def banditFiltration (k : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Fin k × ℝ)) where
  seq n := MeasurableSpace.comap (banditTrajPrefix k n) inferInstance
  mono' a b hab := by
    show MeasurableSpace.comap (banditTrajPrefix k a) inferInstance ≤
      MeasurableSpace.comap (banditTrajPrefix k b) inferInstance
    have h : banditTrajPrefix k a =
        (fun h : BanditHistory k b ↦ fun t : Fin a ↦ h (Fin.castLE hab t)) ∘
          banditTrajPrefix k b := rfl
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      ((measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _).comap_le)
  le' n := measurable_banditTrajPrefix.comap_le

/-- `τ` is a stopping time of the interaction (L&S §33.2): `τ` is adapted to the
natural filtration of the trajectory, with values in `ℕ∞` (`τ = ⊤` = "the learner
never stops", explicitly allowed by the book). -/
abbrev IsBanditStoppingTime {k : ℕ} (τ : (ℕ → Fin k × ℝ) → ℕ∞) : Prop :=
  IsStoppingTime (banditFiltration k) τ

/-- Definition 33.4: the triple `(π, τ, ψ)` of policy, stopping time and selection
rule is *sound* at confidence level `δ` for the environment class `𝓔` if for all
`ν ∈ 𝓔`, `ℙ_{νπ}(τ < ∞ and Δ_{ψ}(ν) > 0) ≤ δ`: whenever the learner stops, the
recommended arm `ψ` is suboptimal with probability at most `δ`. -/
def IsSoundBAI {k : ℕ} (δ : ℝ) (π : BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin k × ℝ) → Fin k) (𝓔 : Set (StochasticBandit k)) : Prop :=
  ∀ ν ∈ 𝓔,
    banditTrajMeasure ν π {ω | τ ω < ⊤ ∧ 0 < banditGap ν (ψ ω)} ≤ ENNReal.ofReal δ

/-- The set `i^*(ν)` of optimal arms of `ν` (L&S p.406). -/
def banditOptimalArms {k : ℕ} (ν : StochasticBandit k) : Set (Fin k) :=
  {i | banditArmMean ν i = banditOptimalMean ν}

/-- The alternative set `𝓔_alt(ν) = {ν' ∈ 𝓔 : i^*(ν') ∩ i^*(ν) = ∅}` of members of
the class whose optimal arms all differ from `ν`'s (L&S p.406). -/
def baiAlternatives {k : ℕ} (𝓔 : Set (StochasticBandit k)) (ν : StochasticBandit k) :
    Set (StochasticBandit k) :=
  {ν' ∈ 𝓔 | Disjoint (banditOptimalArms ν') (banditOptimalArms ν)}

/-- The characteristic time `c^*(ν)` of fixed-confidence best-arm identification
(L&S Eq. (33.4)), defined through
`c^*(ν)⁻¹ = sup_{α ∈ 𝓟_{k-1}} inf_{ν' ∈ 𝓔_alt(ν)} ∑ i, α i · D(ν_i, ν'_i)`.

Conventions (all inherited from `ℝ≥0∞` arithmetic, matching the book): the book
sets `c^*(ν) = ∞` when the displayed supremum is `0` (= `0⁻¹`); if `𝓔_alt(ν) = ∅`
the infimum is `∞` and `c^*(ν) = ∞⁻¹ = 0`. -/
noncomputable def baiComplexity {k : ℕ} (ν : StochasticBandit k)
    (𝓔 : Set (StochasticBandit k)) : ℝ≥0∞ :=
  (⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
      ⨅ ν' ∈ baiAlternatives 𝓔 ν, ∑ i, (α i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i))⁻¹

end BanditAlgorithm


