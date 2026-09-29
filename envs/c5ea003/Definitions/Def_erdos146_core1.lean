-- Prove2me | Definitions.Def_erdos146_core1
-- name    : erdos146_core1
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-04T04:38:11.216934+00:00
-- url     : https://prove2.me/theorems/4c5f217d-d0ac-4a5d-b4e9-3c3524596694
-- title:
--   Degeneracy counterexample: entropy kernel, layered graph and word classification
-- statement:
--   First of two parts of the definitional core for the refutation of Erdős's 2-degenerate extremal conjecture (Erdős problem #146), transplanted from Chapter 10 of OpenAI's *Ten Advances in Mathematics and Theoretical Computer Science*.
--
--   A graph $H$ is **$r$-degenerate** if every nonempty subgraph of $H$ has a vertex of degree at most $r$. Erdős conjectured (Erdős problem #146) that every fixed bipartite $r$-degenerate graph $H$ satisfies $\mathrm{ex}(n,H) = O(n^{2-1/r})$. Chapter 10 of the source disproves this for $r = 2$.
--
--   This part carries three groups of definitions.
--
--   **Binary entropy and the constant $\kappa$.** The binary entropy function $h$, its tangent data and Pinsker-type gap, and the two-bit *pair kernel* of Section 5 — a distribution on a child bit given two parent bits, with its conditional entropy $H(Z \mid X, Y)$, average disagreement, smoothed and empirical variants, and the without-replacement correction of Lemma 5.2 (where an ordered pair of distinct indices is drawn from $x_1,\dots,x_L$). The supremum of the conditional entropy over admissible kernels is the constant $\kappa$ appearing in the threshold $A(\tau) = \kappa + \tau\log_2 3$.
--
--   **Degeneracy and the layered graph.** $r$-degeneracy, 2-degeneracy, the statement of the degeneracy conjecture itself, and the layered construction. The counterexample graph $H$ is built in layers (Section 6): starting from a layer $V_0$ of size $L_0$, each subsequent layer is $V_i = \binom{V_{i-1}}{2}$, and every vertex $\{a,b\} \in V_i$ is joined to its two parents $a, b \in V_{i-1}$. Fact 6.1 records that the result is connected, bipartite and 2-degenerate.
--
--   **Boolean words.** Words of $\{0,1\}^m$ graded by weight, together with the classification of a coordinate of a parent pair into its four outcome types and the induced type-count profiles — the bookkeeping that turns an entropy bound into a count of admissible arrays.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L9384-L12942

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.InformationTheory.Hamming
import Mathlib.Probability.Distributions.SetBernoulli

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  Real.binEntropy x / Real.log 2

noncomputable def tau : ℝ := (Real.sqrt 3 - 1) / 2

noncomputable def kappa : ℝ := 3 / 2 - (3 / 4) * logTwo 3

noncomputable def certifiedWindowWidth : ℝ :=
  logTwo ((97 + 56 * Real.sqrt 3) / 192) / 4

theorem twelve_sevenths_lt_sqrt_three : (12 : ℝ) / 7 < Real.sqrt 3 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  nlinarith

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

noncomputable def binaryPinskerGap (q : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy q - (2 * q - 1) ^ 2 / 2

noncomputable def binaryPinskerGapDeriv (q : ℝ) : ℝ :=
  Real.log q - Real.log (1 - q) - 2 * (2 * q - 1)

noncomputable def binaryPinskerGapDerivTwo (q : ℝ) : ℝ :=
  q⁻¹ + (1 - q)⁻¹ - 4

noncomputable def entropyTangentSigma : ℝ :=
  4 / (3 * Real.sqrt 2)

noncomputable def entropyTangentRho : ℝ :=
  Real.sqrt 2 / Real.sqrt 3

noncomputable def entropyTangentZeroCoefficient (q : ℝ) : ℝ :=
  Real.sqrt 2 * (3 - 2 * q) / 4

noncomputable def entropyTangentOneCoefficient (q : ℝ) : ℝ :=
  Real.sqrt 2 * (1 + 2 * q) / 4

noncomputable def binaryConditionalLogPotential (q zeroAmplitude oneAmplitude : ℝ) : ℝ :=
  Real.binEntropy q / 2 +
    (1 - q) ^ 2 * Real.log (zeroAmplitude + oneAmplitude / 3) +
    q ^ 2 * Real.log (zeroAmplitude / 3 + oneAmplitude) +
    2 * q * (1 - q) *
      Real.log ((zeroAmplitude + oneAmplitude) / Real.sqrt 3)

def binaryCoinMass (q : ℝ) (outcome : Bool) : ℝ :=
  if outcome then q else 1 - q

def independentBinaryPairMass (q : ℝ) (left right : Bool) : ℝ :=
  binaryCoinMass q left * binaryCoinMass q right

structure BinaryPairKernel where
  parentProbability : ℝ
  parentProbability_nonneg : 0 ≤ parentProbability
  parentProbability_le_one : parentProbability ≤ 1
  childProbability : Bool → Bool → ℝ
  childProbability_nonneg : ∀ left right, 0 ≤ childProbability left right
  childProbability_le_one : ∀ left right, childProbability left right ≤ 1

end

namespace BinaryPairKernel
section
open Filter Finset SimpleGraph
open scoped Topology

noncomputable def childMarginal (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      kernel.childProbability left right

noncomputable def conditionalEntropy (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy (kernel.childProbability left right)

def bitDisagreementProbability (parent : Bool) (childProbability : ℝ) : ℝ :=
  if parent then 1 - childProbability else childProbability

noncomputable def averageDisagreement (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      ((bitDisagreementProbability left
          (kernel.childProbability left right) +
        bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)

noncomputable def smoothed (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) : BinaryPairKernel where
  parentProbability := kernel.parentProbability
  parentProbability_nonneg := kernel.parentProbability_nonneg
  parentProbability_le_one := kernel.parentProbability_le_one
  childProbability left right :=
    (1 - mixing) * kernel.childProbability left right + mixing / 2
  childProbability_nonneg := by
    intro left right
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hmixing_one)
        (kernel.childProbability_nonneg left right))
      (div_nonneg hmixing_zero (by norm_num))
  childProbability_le_one := by
    intro left right
    have hproduct := mul_le_mul_of_nonneg_left
      (kernel.childProbability_le_one left right)
      (sub_nonneg.mpr hmixing_one)
    nlinarith

noncomputable def smoothedConditionalEntropy
    (kernel : BinaryPairKernel) (mixing : ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy
        ((1 - mixing) * kernel.childProbability left right + mixing / 2)

end
end BinaryPairKernel

section
open Filter Finset SimpleGraph
open scoped Topology

def empiricalBinaryOutcomeCount
    (parentCount oneCount : ℕ) (outcome : Bool) : ℝ :=
  if outcome then (oneCount : ℝ)
  else (parentCount : ℝ) - (oneCount : ℝ)

noncomputable def withoutReplacementBinaryPairMass
    (parentCount oneCount : ℕ) (left right : Bool) : ℝ :=
  empiricalBinaryOutcomeCount parentCount oneCount left *
      (empiricalBinaryOutcomeCount parentCount oneCount right -
        if left = right then 1 else 0) /
    ((parentCount : ℝ) * ((parentCount : ℝ) - 1))

noncomputable def withoutReplacementBinaryPairExpectation
    (parentCount oneCount : ℕ) (f : Bool → Bool → ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    withoutReplacementBinaryPairMass parentCount oneCount left right *
      f left right

noncomputable def empiricalChildMarginal
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    kernel.childProbability

noncomputable def empiricalConditionalEntropy
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right => binaryEntropy (kernel.childProbability left right))

noncomputable def empiricalAverageDisagreement
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right =>
      (BinaryPairKernel.bitDisagreementProbability left
          (kernel.childProbability left right) +
        BinaryPairKernel.bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)

noncomputable def binomialProbabilityMass
    (trialCount successCount : ℕ) (probability : ℝ) : ℝ :=
  (trialCount.choose successCount : ℝ) *
    probability ^ successCount *
    (1 - probability) ^ (trialCount - successCount)

theorem certificate_ratio_one_lt :
    (1 : ℝ) < (97 + 56 * Real.sqrt 3) / 192 := by
  have h := twelve_sevenths_lt_sqrt_three
  nlinarith

theorem certifiedWindowWidth_pos : 0 < certifiedWindowWidth := by
  unfold certifiedWindowWidth logTwo
  exact div_pos
    (div_pos (Real.log_pos certificate_ratio_one_lt)
      log_two_pos)
    (by norm_num)

theorem tau_pos : 0 < tau := by
  unfold tau
  nlinarith [twelve_sevenths_lt_sqrt_three]

theorem sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := by
  positivity

theorem tau_complement : 1 - tau = Real.sqrt 3 * tau := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  unfold tau
  nlinarith

theorem tau_reciprocal_identity :
    1 + 1 / Real.sqrt 3 = (1 - tau)⁻¹ := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  rw [tau_complement]
  field_simp [sqrt_three_pos.ne', tau_pos.ne']
  unfold tau
  nlinarith

theorem log_three_eq_twice_log_sqrt_three :
    Real.log (3 : ℝ) = 2 * Real.log (Real.sqrt 3) := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  calc
    Real.log (3 : ℝ) = Real.log ((Real.sqrt 3) ^ 2) := by rw [hsqrt_sq]
    _ = 2 * Real.log (Real.sqrt 3) := by
      rw [Real.log_pow]
      ring

theorem entropy_tau_identity :
    2 * binaryEntropy tau - tau * logTwo 3 =
      2 * logTwo (1 + 1 / Real.sqrt 3) := by
  have hlog_complement :
      Real.log (1 - tau) = Real.log (Real.sqrt 3) + Real.log tau := by
    rw [tau_complement, Real.log_mul sqrt_three_pos.ne' tau_pos.ne']
  unfold binaryEntropy logTwo Real.binEntropy
  rw [Real.log_inv, Real.log_inv, tau_reciprocal_identity, Real.log_inv,
    hlog_complement, log_three_eq_twice_log_sqrt_three]
  ring

theorem certificate_ratio_identity :
    (1 + 1 / Real.sqrt 3) ^ (8 : ℕ) * 27 / 1024 =
      (97 + 56 * Real.sqrt 3) / 192 := by
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by positivity)
  have hz : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp [hz]
  ring_nf at hs ⊢
  linear_combination
    (-1728 - 13824 * Real.sqrt 3
      - 48960 * Real.sqrt 3 ^ 2
      - 101376 * Real.sqrt 3 ^ 3
      - 137280 * Real.sqrt 3 ^ 4
      - 130560 * Real.sqrt 3 ^ 5
      - 94144 * Real.sqrt 3 ^ 6
      - 57344 * Real.sqrt 3 ^ 7) * hs

theorem log_certificate_ratio_identity :
    Real.log ((97 + 56 * Real.sqrt 3) / 192) =
      8 * Real.log (1 + 1 / Real.sqrt 3) +
        3 * Real.log 3 - 10 * Real.log 2 := by
  have hu : 0 < (1 : ℝ) + 1 / Real.sqrt 3 := by
    positivity
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    calc
      Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
  have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    calc
      Real.log (1024 : ℝ) = Real.log ((2 : ℝ) ^ (10 : ℕ)) := by norm_num
      _ = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [← certificate_ratio_identity,
    Real.log_div (by positivity) (by norm_num),
    Real.log_mul (by positivity) (by norm_num),
    Real.log_pow, hlog27, hlog1024]
  ring

noncomputable def entropyLowerEndpoint : ℝ := kappa + tau * logTwo 3

noncomputable def entropyUpperEndpoint : ℝ := 2 * binaryEntropy tau - 1

noncomputable def midpointBeta : ℝ :=
  (entropyLowerEndpoint + entropyUpperEndpoint) / 2

theorem entropyWindow_eq_certifiedWindowWidth :
    entropyUpperEndpoint - entropyLowerEndpoint = certifiedWindowWidth := by
  have hentropy := entropy_tau_identity
  have hlog := log_certificate_ratio_identity
  unfold logTwo at hentropy
  have hlog_argument :
      (Real.sqrt 3 + 1) / Real.sqrt 3 =
        1 + 1 / Real.sqrt 3 := by
    field_simp [sqrt_three_pos.ne']
  unfold entropyUpperEndpoint entropyLowerEndpoint kappa
    certifiedWindowWidth logTwo
  field_simp [log_two_pos.ne'] at hentropy ⊢
  rw [hlog_argument] at hentropy
  ring_nf at hentropy hlog ⊢
  linarith

theorem entropyWindow_pos : entropyLowerEndpoint < entropyUpperEndpoint := by
  have h := certifiedWindowWidth_pos
  rw [← entropyWindow_eq_certifiedWindowWidth] at h
  linarith

theorem midpointBeta_gt_lower
    (hwindow : entropyLowerEndpoint < entropyUpperEndpoint) :
    entropyLowerEndpoint < midpointBeta := by
  unfold midpointBeta
  linarith

theorem midpointBeta_gt_lower_unconditional :
    entropyLowerEndpoint < midpointBeta :=
  midpointBeta_gt_lower entropyWindow_pos

theorem logTwo_three_pos : 0 < logTwo 3 := by
  unfold logTwo
  exact div_pos (Real.log_pos (by norm_num)) log_two_pos

theorem logTwo_three_lt_two : logTwo 3 < 2 := by
  have hlog : Real.log (3 : ℝ) < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  unfold logTwo
  apply (div_lt_iff₀ log_two_pos).mpr
  nlinarith [hlog]

theorem kappa_pos : 0 < kappa := by
  unfold kappa
  nlinarith [logTwo_three_lt_two]

theorem entropyLowerEndpoint_pos : 0 < entropyLowerEndpoint := by
  unfold entropyLowerEndpoint
  positivity [kappa_pos, tau_pos, logTwo_three_pos]

theorem midpointBeta_pos : 0 < midpointBeta :=
  entropyLowerEndpoint_pos.trans midpointBeta_gt_lower_unconditional

noncomputable def entropySlack : ℝ := certifiedWindowWidth / 8

noncomputable def exponentGain : ℝ :=
  certifiedWindowWidth / (8 * (1 - midpointBeta))

noncomputable def empiricalEntropyError (layerSize : ℕ) : ℝ :=
  (1 + logTwo 3) / (layerSize : ℝ) +
    binaryEntropy (1 / (layerSize : ℝ)) / 2

noncomputable def neighborsWithin {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (v : V) : Finset V := by
  classical
  exact s.filter (G.Adj v)

def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r

abbrev IsTwoDegenerate {V : Type*} (G : SimpleGraph V) : Prop :=
  IsDegenerate 2 G

def DegeneracyConjectureStatement : Prop :=
  ∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
    0 < r → H.IsBipartite → IsDegenerate r H →
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ))
        (fun n : ℕ => (n : ℝ) ^ (((2 : ℕ) : ℝ) - 1 / (r : ℝ)))

structure ParentSystem (V : Type*) where
  level : V → ℕ
  parents : V → Finset V
  parent_level : ∀ ⦃v u : V⦄, u ∈ parents v → level u + 1 = level v
  parent_card : ∀ v : V, (parents v).card ≤ 2

end

namespace ParentSystem
section
open Filter Finset SimpleGraph
open scoped Topology

def graph {V : Type*} (P : ParentSystem V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v u => u ∈ P.parents v)

end
end ParentSystem

section
open Filter Finset SimpleGraph
open scoped Topology

def PairLayer (baseSize : ℕ) : ℕ → Type
  | 0 => Fin baseSize
  | i + 1 => {parents : Finset (PairLayer baseSize i) // parents.card = 2}

noncomputable instance pairLayerFintype (baseSize i : ℕ) :
    Fintype (PairLayer baseSize i) := by
  classical
  induction i with
  | zero =>
      change Fintype (Fin baseSize)
      infer_instance
  | succ i ih =>
      letI := ih
      change Fintype
        {parents : Finset (PairLayer baseSize i) // parents.card = 2}
      infer_instance

theorem pairLayer_card_zero (baseSize : ℕ) :
    Fintype.card (PairLayer baseSize 0) = baseSize := by
  change Fintype.card (Fin baseSize) = baseSize
  simp

theorem pairLayer_card_succ (baseSize i : ℕ) :
    Fintype.card (PairLayer baseSize (i + 1)) =
      (Fintype.card (PairLayer baseSize i)).choose 2 := by
  classical
  let layerPairs : Finset (Finset (PairLayer baseSize i)) :=
    (Finset.univ : Finset (PairLayer baseSize i)).powersetCard 2
  let equivalence : PairLayer baseSize (i + 1) ≃ layerPairs :=
    { toFun := fun p =>
        ⟨p.val, by
          apply Finset.mem_powersetCard.mpr
          exact ⟨Finset.subset_univ _, p.property⟩⟩
      invFun := fun p => ⟨p.val, (Finset.mem_powersetCard.mp p.property).2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  calc
    Fintype.card (PairLayer baseSize (i + 1)) = Fintype.card layerPairs :=
      Fintype.card_congr equivalence
    _ = layerPairs.card := Fintype.card_coe layerPairs
    _ = (Fintype.card (PairLayer baseSize i)).choose 2 := by
      simp [layerPairs]

theorem le_choose_two_of_four {size : ℕ} (hsize : 4 ≤ size) :
    size ≤ size.choose 2 := by
  have hreal : (4 : ℝ) ≤ (size : ℝ) := by
    exact_mod_cast hsize
  have hchoose :
      (size.choose 2 : ℝ) =
        (size : ℝ) * ((size : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ size
  have hbound : (size : ℝ) ≤ (size.choose 2 : ℝ) := by
    rw [hchoose]
    nlinarith [sq_nonneg ((size : ℝ) - 2)]
  exact_mod_cast hbound

theorem pairLayer_card_ge_base
    (baseSize i : ℕ) (hbase : 4 ≤ baseSize) :
    baseSize ≤ Fintype.card (PairLayer baseSize i) := by
  induction i with
  | zero =>
      rw [pairLayer_card_zero]
  | succ i ih =>
      rw [pairLayer_card_succ]
      exact ih.trans
        (le_choose_two_of_four (hbase.trans ih))

noncomputable def pairLayerFinEquiv (baseSize layer : ℕ) :
    PairLayer baseSize layer ≃
      Fin (Fintype.card (PairLayer baseSize layer)) :=
  Fintype.equivFin (PairLayer baseSize layer)

noncomputable def pairLayerPairEquiv (baseSize layer : ℕ) :
    PairLayer (Fintype.card (PairLayer baseSize layer)) 1 ≃
      PairLayer baseSize (layer + 1) := by
  classical
  change
    {parents : Finset
      (Fin (Fintype.card (PairLayer baseSize layer))) //
        parents.card = 2} ≃
      {parents : Finset (PairLayer baseSize layer) //
        parents.card = 2}
  exact
    (pairLayerFinEquiv baseSize layer).symm.finsetCongr.subtypeEquiv
      (fun parents => by
        simp [Equiv.finsetCongr_apply])

abbrev PairVertex (baseSize depth : ℕ) :=
  Σ i : Fin (depth + 1), PairLayer baseSize i.val

def pairLayerEmbedding (baseSize depth i : ℕ) (hi : i < depth + 1) :
    PairLayer baseSize i ↪ PairVertex baseSize depth where
  toFun v := ⟨⟨i, hi⟩, v⟩
  inj' := by
    intro v w heq
    cases heq
    rfl

noncomputable def pairParents (baseSize depth : ℕ) :
    PairVertex baseSize depth → Finset (PairVertex baseSize depth)
  | ⟨⟨0, _⟩, _⟩ => ∅
  | ⟨⟨i + 1, hi⟩, v⟩ =>
      v.val.map (pairLayerEmbedding baseSize depth i (by omega))

noncomputable def pairParentSystem (baseSize depth : ℕ) :
    ParentSystem (PairVertex baseSize depth) where
  level v := v.1.val
  parents := pairParents baseSize depth
  parent_level := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩ ⟨⟨j, hj⟩, u⟩ hparent
    cases i with
    | zero =>
        simp [pairParents] at hparent
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp only [pairParents, Finset.mem_map] at hparent
        obtain ⟨w, _, hw⟩ := hparent
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) hw
        change i = j at hlevels
        change j + 1 = i + 1
        omega
  parent_card := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩
    cases i with
    | zero =>
        simp [pairParents]
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp [pairParents, v.property]

def pairBaseVertex (baseSize depth : ℕ) (a : Fin baseSize) :
    PairVertex baseSize depth :=
  pairLayerEmbedding baseSize depth 0 (by omega) a

noncomputable def pairGraphOverFin (baseSize depth : ℕ) :
    SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
  (pairParentSystem baseSize depth).graph.overFin rfl

noncomputable def pairGraphOverFinIso (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph ≃g
      pairGraphOverFin baseSize depth :=
  (pairParentSystem baseSize depth).graph.overFinIso rfl

abbrev HammingWord (dimension : ℕ) := Fin dimension → Bool

noncomputable def booleanWordOnes {ι : Type*} [Fintype ι]
    (word : ι → Bool) : Finset ι := by
  classical
  exact Finset.univ.filter (fun index => word index = true)

noncomputable def booleanWordsOfWeight (ι : Type*) [Fintype ι]
    (weight : ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => (booleanWordOnes word).card = weight)

noncomputable def booleanWordsOfWeightEquiv
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    ↥(booleanWordsOfWeight ι weight) ≃
      ↥((Finset.univ : Finset ι).powersetCard weight) := by
  classical
  refine
    { toFun := fun word => ⟨booleanWordOnes word.val, ?_⟩
      invFun := fun support =>
        ⟨fun index => decide (index ∈ support.val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hword :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              (booleanWordOnes candidate).card = weight)) := by
      simpa only [booleanWordsOfWeight] using word.property
    exact (Finset.mem_filter.mp hword).2
  · have hsupport :=
      (Finset.mem_powersetCard.mp support.property).2
    have hones :
        booleanWordOnes
          (fun index : ι => decide (index ∈ support.val)) = support.val := by
      ext index
      simp [booleanWordOnes]
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hones]
    exact hsupport
  · intro word
    apply Subtype.ext
    funext index
    cases hbit : word.val index <;>
      simp [booleanWordOnes, hbit]
  · intro support
    apply Subtype.ext
    ext index
    simp [booleanWordOnes]

abbrev ClassificationFiber
    {ι γ : Type*} (classify : ι → γ) (group : γ) :=
  {index : ι // classify index = group}

noncomputable def classificationGroup
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) : Finset ι :=
  Finset.univ.filter (fun index => classify index = group)

noncomputable def classifiedWordOnes
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) : Finset ι :=
  (classificationGroup classify group).filter
    (fun index => word index = true)

noncomputable def classifiedWordSupportEquiv
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    ↥(booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)) ≃
      ↥(classifiedWordOnes classify group word) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.val, ?_⟩
      invFun := fun index => ⟨⟨index.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hbit : word index.val.val = true := by
      have hmembership :
          index.val ∈
            (Finset.univ.filter
              (fun candidate : ClassificationFiber classify group =>
                word candidate.val = true)) := by
        simpa only [booleanWordOnes] using index.property
      exact (Finset.mem_filter.mp hmembership).2
    simp [classifiedWordOnes, classificationGroup,
      index.val.property, hbit]
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hgroup := (Finset.mem_filter.mp hmembership).1
    exact (Finset.mem_filter.mp hgroup).2
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hbit := (Finset.mem_filter.mp hmembership).2
    simp [booleanWordOnes, hbit]
  · intro index
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro index
    apply Subtype.ext
    rfl

theorem classifiedWordOnes_card
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    (classifiedWordOnes classify group word).card =
      (booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)).card := by
  calc
    (classifiedWordOnes classify group word).card =
        Fintype.card ↥(classifiedWordOnes classify group word) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥(booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)) :=
      Fintype.card_congr
        (classifiedWordSupportEquiv classify group word).symm
    _ = (booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)).card :=
      Fintype.card_coe _

noncomputable def classifiedBooleanWords
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => ∀ group,
      (classifiedWordOnes classify group word).card = counts group)

noncomputable def classifiedBooleanWordsEquiv
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    ↥(classifiedBooleanWords classify counts) ≃
      (∀ group : γ,
        ↥(booleanWordsOfWeight
          (ClassificationFiber classify group) (counts group))) := by
  classical
  refine
    { toFun := fun word group =>
        ⟨fun index => word.val index.val, ?_⟩
      invFun := fun pieces =>
        ⟨fun index => (pieces (classify index)).val ⟨index, rfl⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              ∀ group,
                (classifiedWordOnes classify group candidate).card =
                  counts group)) := by
      simpa only [classifiedBooleanWords] using word.property
    have hprofile := (Finset.mem_filter.mp hmembership).2 group
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (classifiedWordOnes_card classify group word.val).symm.trans
      hprofile
  · simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro group
    rw [classifiedWordOnes_card]
    have hrestriction :
        (fun index : ClassificationFiber classify group =>
          (pieces (classify index.val)).val
            ⟨index.val, rfl⟩) =
          (pieces group).val := by
      funext index
      rcases index with ⟨index, hindex⟩
      cases hindex
      rfl
    rw [hrestriction]
    have hmembership := (pieces group).property
    unfold booleanWordsOfWeight at hmembership
    exact (Finset.mem_filter.mp hmembership).2
  · intro word
    apply Subtype.ext
    funext index
    rfl
  · intro pieces
    funext group
    apply Subtype.ext
    funext index
    rcases index with ⟨index, hindex⟩
    cases hindex
    rfl

abbrev PairBitType := Fin 3

abbrev PairTypeCountProfile (parentCount dimension : ℕ) :=
  PairBitType → Fin dimension → Fin (parentCount.choose 2 + 1)

noncomputable def pairCoordinateBitType
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : PairBitType := by
  classical
  exact
    if ∀ parent ∈ pair.val, parents parent coordinate = false then 0
    else if ∀ parent ∈ pair.val, parents parent coordinate = true then 1
    else 2

noncomputable def pairTypeGroup
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact Finset.univ.filter
    (fun pair => pairCoordinateBitType parents coordinate pair = bitType)

noncomputable def pairCoordinateClassification
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → PairBitType × Fin dimension :=
  fun index =>
    (pairCoordinateBitType parents index.2 index.1, index.2)

noncomputable def pairCoordinateClassificationFiberEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate) ≃
      ↥(pairTypeGroup parents coordinate bitType) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.1, ?_⟩
      invFun := fun pair => ⟨(pair.val, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have htype := congrArg Prod.fst index.property
    have hcoordinate : index.val.2 = coordinate := by
      simpa [pairCoordinateClassification] using
        congrArg Prod.snd index.property
    simp only [pairTypeGroup, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [pairCoordinateClassification, hcoordinate] using htype
  · have hmembership :
        pair.val ∈
          (Finset.univ.filter
            (fun candidate : PairLayer parentCount 1 =>
              pairCoordinateBitType parents coordinate candidate = bitType)) := by
      simpa only [pairTypeGroup] using pair.property
    have htype := (Finset.mem_filter.mp hmembership).2
    change
      (pairCoordinateBitType parents coordinate pair.val, coordinate) =
        (bitType, coordinate)
    exact Prod.ext htype rfl
  · intro index
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hcoordinate := congrArg Prod.snd index.property
      simpa [pairCoordinateClassification] using hcoordinate.symm
  · intro pair
    apply Subtype.ext
    rfl

theorem pairTypeGroup_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroup parents coordinate bitType).card ≤
      parentCount.choose 2 := by
  classical
  calc
    (pairTypeGroup parents coordinate bitType).card ≤
      (Finset.univ : Finset (PairLayer parentCount 1)).card := by
        unfold pairTypeGroup
        exact Finset.card_filter_le _ _
    _ = parentCount.choose 2 := by
      rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
        pairLayer_card_zero]

noncomputable def pairTypeGroupChildOnes
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact (pairTypeGroup parents coordinate bitType).filter
    (fun pair => children pair coordinate = true)

end

end Erdos146


