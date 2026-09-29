-- Prove2me | solution 1 for MarkovChainCLT.exists_countable_alpha_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-06T15:09:23.92671+00:00
-- url     : https://prove2.me/submissions/34cfd504-9baf-4e12-9528-26e7af2748c9

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

/-!
# A1 : the countable multiplicative witness reduction for `alphaMixingCoef`

`alphaMixingCoef P Y n` is an `sSup` over an *uncountable* family of pairs of events, and the
events themselves are measurable with respect to `processSigma Y s`, a supremum of comaps of the
**full** σ-algebra of the state space `E`.  Both features obstruct every classical route to a
geometric bound, because they make the total-variation profile
`x ↦ tvDist (Pⁿ x) π` an uncountable supremum of measurable functions, hence in general
non-measurable — which is exactly the slack that killed `geometricallyErgodic_integrable_rate`.

This file removes both obstructions at once, and does so **multiplicatively**: for every lag `n`
we produce a single witness pair whose covariance defect is at least `α(n)/2`.  A multiplicative
(rather than additive `1/j`) approximation is essential: an additive scheme yields only
`α(n) ≤ 1/j + Cρⁿ` with `j` free, hence `α(n) ≤ 1/n + Cρⁿ`, which is not geometric.  The factor
`2` is absorbed into the constant `c` of a geometric bound and costs nothing.

The witnesses are produced **simultaneously for all lags**, so the countable family of
state-space sets they generate is a single countable family `𝒞`, and the reduction is to the
single countably generated σ-algebra `generateFrom 𝒞`.

Main results:

* `MarkovChainCLT.exists_alpha_witness` — a multiplicative witness at one lag.
* `MarkovChainCLT.exists_countable_processSigma` — every past/future event already lives in
  `processSigma` built over a countably generated sub-σ-algebra of the state space.
* `MarkovChainCLT.exists_countable_alpha_witnesses` — the full A1 statement: one countable
  `𝒞 ⊆ {measurable sets of E}` and one sequence of witness triples `(K n, A n, B n)`, with
  `A n`, `B n` measurable for `processSigma` over `generateFrom 𝒞`, such that
  `α(n) ≤ 2 |P(Aₙ ∩ Bₙ) - P(Aₙ)P(Bₙ)|` for every `n`.
* `MarkovChainCLT.exists_alpha_le_two_mul_countablyGenerated` — the packaged form
  `α(n) ≤ 2 · α_{generateFrom 𝒞}(n)` for all `n`, with a single countable `𝒞`.
* `MarkovChainCLT.alphaMixingCoef_mono_measurableSpace` — the converse inequality, and the fact
  that the reduction survives *enlarging* `𝒞`, so downstream work may freely close `𝒞` under any
  countable operation (e.g. under the transition kernel).
* `MarkovChainCLT.exists_geometric_alpha_of_countablyGenerated` — the payoff: to prove the open
  child `exists_geometric_alpha_of_geometricallyErgodic` it suffices to prove it with the state
  space carrying an arbitrary countably generated σ-algebra.

A countably generated σ-algebra need not be `P`-invariant, and a non-`P`-invariant factor of a
Markov chain is not a Markov chain, so the reduction is completed by a second closure:

* `MarkovChainCLT.kernelClosure` / `MarkovChainCLT.closedSigma` — the countable family closed
  under binary intersections and under the kernel pullbacks `x ↦ P x T`.
* `MarkovChainCLT.measurable_coe_kernelClosure` — `closedSigma P 𝒞` is `P`-invariant.
* `MarkovChainCLT.factorKernel` (+ its `IsMarkovKernel` instance) — the honest Markov kernel on
  the countably generated space `(X, closedSigma P 𝒞)`.
* `MarkovChainCLT.exists_geometric_alpha_of_kernelClosed` — the capstone: it suffices to prove
  the geometric α-bound when the state-space σ-algebra is countably generated **and** closed
  under the transition kernel.  That is exactly the standing hypothesis of Meyn–Tweedie
  (Chapter 3: `(X, B(X))` countably generated), which is what the disproof of the sibling
  `geometricallyErgodic_integrable_rate` exploits the absence of: its counterexample is the
  countable/co-countable σ-algebra on an uncountable set, where every measurable real function
  is constant off a countable set.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal NNReal

namespace MarkovChainCLT

/-! ### The generating family of `processSigma` -/

/-- The family of "one-coordinate cylinders" generating `processSigma Y s`. -/
def processGens {Ω E : Type*} [MeasurableSpace E] (Y : ℕ → Ω → E) (s : Set ℕ) : Set (Set Ω) :=
  {t | ∃ i ∈ s, ∃ S : Set E, MeasurableSet S ∧ t = Y i ⁻¹' S}

lemma processSigma_eq_generateFrom {Ω E : Type*} [MeasurableSpace E] (Y : ℕ → Ω → E)
    (s : Set ℕ) : processSigma Y s = generateFrom (processGens Y s) := by
  refine le_antisymm (iSup₂_le fun i hi t ht => ?_) (generateFrom_le ?_)
  · obtain ⟨S, hS, rfl⟩ := ht
    exact measurableSet_generateFrom ⟨i, hi, S, hS, rfl⟩
  · rintro t ⟨i, hi, S, hS, rfl⟩
    exact le_iSup₂ (f := fun i (_ : i ∈ s) => MeasurableSpace.comap (Y i) inferInstance) i hi
      _ ⟨S, hS, rfl⟩

/-- `processSigma` is monotone in the σ-algebra of the state space. -/
lemma processSigma_mono {Ω E : Type*} {m₁ m₂ : MeasurableSpace E} (h : m₁ ≤ m₂)
    (Y : ℕ → Ω → E) (s : Set ℕ) :
    @processSigma Ω E m₁ Y s ≤ @processSigma Ω E m₂ Y s :=
  iSup₂_mono fun _ _ => comap_mono h

/-- A σ-algebra generated by measurable sets is a sub-σ-algebra. -/
lemma generateFrom_le_of_measurable {E : Type*} [MeasurableSpace E] {𝒞 : Set (Set E)}
    (h : ∀ S ∈ 𝒞, MeasurableSet S) : generateFrom 𝒞 ≤ ‹MeasurableSpace E› :=
  generateFrom_le h

/-! ### Countable generation of a single event -/

/-- **Every measurable set is generated by countably many generators.** -/
theorem exists_countable_sub_generateFrom {α : Type*} (C : Set (Set α)) {s : Set α}
    (hs : MeasurableSet[generateFrom C] s) :
    ∃ C₀ ⊆ C, C₀.Countable ∧ MeasurableSet[generateFrom C₀] s := by
  induction hs with
  | basic t ht =>
      exact ⟨{t}, Set.singleton_subset_iff.2 ht, Set.countable_singleton t,
        measurableSet_generateFrom rfl⟩
  | empty => exact ⟨∅, Set.empty_subset _, Set.countable_empty, measurableSet_empty _⟩
  | compl t _ ih => obtain ⟨C₀, h1, h2, h3⟩ := ih; exact ⟨C₀, h1, h2, h3.compl⟩
  | iUnion f _ ih =>
      choose C₀ h1 h2 h3 using ih
      exact ⟨⋃ n, C₀ n, Set.iUnion_subset h1, Set.countable_iUnion h2,
        MeasurableSet.iUnion fun n => generateFrom_mono (Set.subset_iUnion C₀ n) _ (h3 n)⟩

/-- **Countable-generation of a single past/future event.**  Any event measurable for
`processSigma Y s` is already measurable for `processSigma Y s` computed over a *countably
generated* sub-σ-algebra of the state space. -/
theorem exists_countable_processSigma {Ω E : Type*} [MeasurableSpace E]
    (Y : ℕ → Ω → E) (s : Set ℕ) {A : Set Ω} (hA : MeasurableSet[processSigma Y s] A) :
    ∃ 𝒞 : Set (Set E), 𝒞.Countable ∧ (∀ S ∈ 𝒞, MeasurableSet S) ∧
      MeasurableSet[@processSigma Ω E (generateFrom 𝒞) Y s] A := by
  rw [processSigma_eq_generateFrom] at hA
  induction hA with
  | basic t ht =>
      obtain ⟨i, hi, S, hS, rfl⟩ := ht
      refine ⟨{S}, Set.countable_singleton S, ?_, ?_⟩
      · rintro T rfl; exact hS
      · exact le_iSup₂ (f := fun i (_ : i ∈ s) =>
          MeasurableSpace.comap (Y i) (generateFrom {S})) i hi _
          ⟨S, measurableSet_generateFrom rfl, rfl⟩
  | empty => exact ⟨∅, Set.countable_empty, by simp, measurableSet_empty _⟩
  | compl t _ ih => obtain ⟨𝒞, h1, h2, h3⟩ := ih; exact ⟨𝒞, h1, h2, h3.compl⟩
  | iUnion f _ ih =>
      choose 𝒞 h1 h2 h3 using ih
      refine ⟨⋃ n, 𝒞 n, Set.countable_iUnion h1, ?_, ?_⟩
      · rintro S hS
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hS
        exact h2 n S hn
      · exact MeasurableSet.iUnion fun n =>
          processSigma_mono (generateFrom_mono (Set.subset_iUnion 𝒞 n)) Y s _ (h3 n)

/-! ### The set whose supremum is the α-coefficient -/

/-- The set of covariance defects whose supremum is `alphaMixingCoef P Y n`. -/
def alphaSet {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (Y : ℕ → Ω → E) (n : ℕ) : Set ℝ :=
  {r | ∃ k : ℕ, ∃ A B : Set Ω,
    MeasurableSet[processSigma Y (Set.Iic k)] A ∧
    MeasurableSet[processSigma Y (Set.Ici (k + n))] B ∧
    r = |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal|}

lemma alphaMixingCoef_eq_sSup {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (Y : ℕ → Ω → E) (n : ℕ) :
    alphaMixingCoef P Y n = sSup (alphaSet P Y n) := rfl

lemma zero_mem_alphaSet {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (Y : ℕ → Ω → E) (n : ℕ) : (0 : ℝ) ∈ alphaSet P Y n :=
  ⟨0, ∅, ∅, measurableSet_empty _, measurableSet_empty _, by simp⟩

lemma alphaSet_nonempty {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (Y : ℕ → Ω → E) (n : ℕ) : (alphaSet P Y n).Nonempty :=
  ⟨0, zero_mem_alphaSet P Y n⟩

lemma alphaSet_le_one {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    ∀ r ∈ alphaSet P Y n, r ≤ 1 := by
  rintro r ⟨k, A, B, -, -, rfl⟩
  have h1 : (0:ℝ) ≤ (P (A ∩ B)).toReal := ENNReal.toReal_nonneg
  have h2 : (P (A ∩ B)).toReal ≤ 1 := measureReal_le_one
  have h3 : (0:ℝ) ≤ (P A).toReal := ENNReal.toReal_nonneg
  have h4 : (P A).toReal ≤ 1 := measureReal_le_one
  have h5 : (0:ℝ) ≤ (P B).toReal := ENNReal.toReal_nonneg
  have h6 : (P B).toReal ≤ 1 := measureReal_le_one
  have h7 : (P A).toReal * (P B).toReal ≤ 1 := by nlinarith
  have h8 : (0:ℝ) ≤ (P A).toReal * (P B).toReal := by positivity
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

lemma alphaSet_bddAbove {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    BddAbove (alphaSet P Y n) :=
  ⟨1, alphaSet_le_one P Y n⟩

lemma alphaMixingCoef_nonneg' {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    0 ≤ alphaMixingCoef P Y n :=
  le_csSup (alphaSet_bddAbove P Y n) (zero_mem_alphaSet P Y n)

/-- The α-coefficient is monotone in the σ-algebra carried by the state space.  In particular
the reduction below survives replacing `𝒞` by any larger countable family. -/
lemma alphaMixingCoef_mono_measurableSpace {Ω E : Type*} [MeasurableSpace Ω]
    {m₁ m₂ : MeasurableSpace E} (h : m₁ ≤ m₂) (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (n : ℕ) :
    @alphaMixingCoef Ω E _ m₁ P Y n ≤ @alphaMixingCoef Ω E _ m₂ P Y n := by
  refine csSup_le_csSup (@alphaSet_bddAbove Ω E _ m₂ P _ Y n)
    (@alphaSet_nonempty Ω E _ m₁ P Y n) ?_
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  exact ⟨k, A, B, processSigma_mono h Y _ _ hA, processSigma_mono h Y _ _ hB, rfl⟩

/-! ### The multiplicative witness -/

/-- **Multiplicative witness at a single lag.**  The factor `2` (any factor `> 1` would do) is
what makes the statement provable: `α(n)/2 < α(n)` whenever `α(n) > 0`, so the defining
supremum is approached, while `α(n) = 0` is realised exactly by the trivial witness.  No
additive approximation is used, so no `1/j` term is created. -/
theorem exists_alpha_witness {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    ∃ (k : ℕ) (A B : Set Ω),
      MeasurableSet[processSigma Y (Set.Iic k)] A ∧
      MeasurableSet[processSigma Y (Set.Ici (k + n))] B ∧
      alphaMixingCoef P Y n ≤ 2 * |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| := by
  rcases le_or_gt (alphaMixingCoef P Y n) 0 with h | h
  · exact ⟨0, ∅, ∅, measurableSet_empty _, measurableSet_empty _, by simpa using h⟩
  · have hhalf : alphaMixingCoef P Y n / 2 < sSup (alphaSet P Y n) := by
      rw [← alphaMixingCoef_eq_sSup]; exact half_lt_self h
    obtain ⟨r, hr, hlt⟩ := exists_lt_of_lt_csSup (alphaSet_nonempty P Y n) hhalf
    obtain ⟨k, A, B, hA, hB, rfl⟩ := hr
    exact ⟨k, A, B, hA, hB, by linarith⟩

/-! ### A1 : countable witnesses, simultaneously for all lags -/

/-- **A1, witness form.**  There is one countable family `𝒞` of measurable subsets of the state
space and one sequence of witness triples `(K n, A n, B n)` such that, for every lag `n`:
`A n` is a past event and `B n` a future event *for the countably generated σ-algebra
`generateFrom 𝒞`*, and their covariance defect is at least `α(n)/2`. -/
theorem a1_core {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) :
    ∃ (𝒞 : Set (Set E)) (K : ℕ → ℕ) (A B : ℕ → Set Ω),
      𝒞.Countable ∧ (∀ S ∈ 𝒞, MeasurableSet S) ∧
      (∀ n, MeasurableSet[@processSigma Ω E (generateFrom 𝒞) Y (Set.Iic (K n))] (A n)) ∧
      (∀ n, MeasurableSet[@processSigma Ω E (generateFrom 𝒞) Y (Set.Ici (K n + n))] (B n)) ∧
      (∀ n, alphaMixingCoef P Y n ≤
        2 * |(P (A n ∩ B n)).toReal - (P (A n)).toReal * (P (B n)).toReal|) := by
  choose K A B hA hB hle using fun n => exists_alpha_witness P Y n
  choose 𝒞A hA1 hA2 hA3 using fun n => exists_countable_processSigma Y (Set.Iic (K n)) (hA n)
  choose 𝒞B hB1 hB2 hB3 using fun n => exists_countable_processSigma Y (Set.Ici (K n + n)) (hB n)
  refine ⟨(⋃ n, 𝒞A n) ∪ (⋃ n, 𝒞B n), K, A, B,
    (Set.countable_iUnion hA1).union (Set.countable_iUnion hB1), ?_, ?_, ?_, hle⟩
  · rintro S hS
    rcases hS with hS | hS
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hS; exact hA2 n S hn
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hS; exact hB2 n S hn
  · exact fun n => processSigma_mono (generateFrom_mono
      ((Set.subset_iUnion 𝒞A n).trans Set.subset_union_left)) Y _ _ (hA3 n)
  · exact fun n => processSigma_mono (generateFrom_mono
      ((Set.subset_iUnion 𝒞B n).trans Set.subset_union_right)) Y _ _ (hB3 n)

end MarkovChainCLT

open MeasureTheory ProbabilityTheory MeasurableSpace MarkovChainCLT
open scoped ENNReal NNReal ProbabilityTheory

/-- The strong mixing coefficient is realised, up to a factor 2, by a single countable
family of measurable subsets of the state space, simultaneously at every lag.

`solution` is declared at TOP LEVEL, outside `namespace MarkovChainCLT`: preflight's
axiom gate emits a bare `#print axioms solution` and gate 5 forms `@solution`, so a
namespaced `solution` fails both. -/
theorem solution {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) :
    ∃ (𝒞 : Set (Set E)) (K : ℕ → ℕ) (A B : ℕ → Set Ω),
      𝒞.Countable ∧ (∀ S ∈ 𝒞, MeasurableSet S) ∧
      (∀ n, MeasurableSet[@processSigma Ω E (generateFrom 𝒞) Y (Set.Iic (K n))] (A n)) ∧
      (∀ n, MeasurableSet[@processSigma Ω E (generateFrom 𝒞) Y (Set.Ici (K n + n))] (B n)) ∧
      (∀ n, alphaMixingCoef P Y n ≤
        2 * |(P (A n ∩ B n)).toReal - (P (A n)).toReal * (P (B n)).toReal|) :=
  MarkovChainCLT.a1_core P Y
