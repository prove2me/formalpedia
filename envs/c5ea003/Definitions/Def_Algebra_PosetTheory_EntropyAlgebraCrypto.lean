-- Prove2me | Definitions.Def_Algebra_PosetTheory_EntropyAlgebraCrypto
-- name    : Algebra_PosetTheory_EntropyAlgebraCrypto
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:49:04.676485+00:00
-- url     : https://prove2.me/theorems/ba5dc791-8283-4113-8b8e-85e370e85e31
-- title:
--   Aether Catalog definitions — Algebra_PosetTheory_EntropyAlgebraCrypto
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetTheory.EntropyAlgebraCrypto`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetTheory/EntropyAlgebraCrypto.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.

# Entropy-Algebra-Cryptography Bridge: Information-Theoretic Shared Structures

## Overview

This file establishes a foundational framework connecting three domains:
- **Information Theory**: Shannon entropy, min-entropy, and channel capacity bounds
- **Algebra**: Lattice-theoretic structures on entropy spaces, semiring homomorphisms
- **Cryptography**: Post-quantum security parameters, hash collision bounds

## Bridge: connects InformationTheory to Algebra to Cryptography

The central insight is that entropy functions induce a natural partial order on
probability distributions, forming a lattice structure whose algebraic properties
yield both information-theoretic inequalities and cryptographic security bounds.

## Key Results

1. Entropy chain rule decomposition with explicit O(n) complexity bounds
2. Lattice structure on entropy-bounded distribution spaces
3. Post-quantum security reduction via min-entropy extraction
4. Lipschitz continuity of entropy maps (certified robustness for ML)
5. Tropical encoding of channel capacity with algebraic completeness

## Applications

- **Cryptography**: Entropy-based key derivation security bounds
- **Machine Learning**: Lipschitz-certified robustness via entropy regularization
- **Physics**: Thermodynamic free energy as tropical entropy
-/

open Finset Real BigOperators

noncomputable section

namespace EntropyAlgebraCrypto

/-! ## Section 1: Entropy Lattice Foundations

We define an abstract entropy measure as a function on finite probability vectors
satisfying subadditivity and monotonicity, then show these form a lattice under
the natural information ordering. -/

/-- An entropy measure on vectors of length n, abstracting Shannon/Rényi/min-entropy.
    Bridge: connects InformationTheory (entropy axioms) to Algebra (ordered monoid). -/
structure EntropyMeasure (n : ℕ) where
  /-- The entropy function maps probability-like vectors to ℝ -/
  eval : (Fin n → ℝ) → ℝ
  /-- Entropy is nonneg for nonneg inputs -/
  nonneg : ∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i) → 0 ≤ eval p
  /-- Entropy is bounded by log of support size -/
  bounded : ∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i) → eval p ≤ n


/-- The entropy gap between two measures — quantifies information leakage.
    Central to both channel coding theorems and cryptographic reductions.
    Bridge: connects InformationTheory to Cryptography (leakage bounds). -/
def entropyGap {n : ℕ} (μ₁ μ₂ : EntropyMeasure n) (p : Fin n → ℝ) : ℝ :=
  μ₁.eval p - μ₂.eval p


/-! ## Section 2: Channel Capacity Algebra

We formalize discrete memoryless channels and prove capacity bounds
with explicit computational complexity. -/

/-- A discrete memoryless channel from input alphabet of size m to output of size n.
    The transition matrix rows are probability distributions.
    Bridge: connects InformationTheory (channels) to Algebra (matrix theory). -/
structure DiscreteChannel (m n : ℕ) where
  /-- Transition probabilities: trans i j = P(output j | input i) -/
  trans : Fin m → Fin n → ℝ
  /-- Probabilities are nonneg -/
  nonneg : ∀ i j, 0 ≤ trans i j
  /-- Rows sum to at most 1 (sub-stochastic allowed) -/
  row_sum_le : ∀ i, ∑ j : Fin n, trans i j ≤ 1

/-- The maximum output probability for a channel, bounding capacity.
    Bridge: connects InformationTheory (capacity) to Cryptography (advantage bounds). -/
def channelMaxProb {m n : ℕ} (ch : DiscreteChannel m n) : ℝ :=
  if h : 0 < m ∧ 0 < n then
    haveI : Nonempty (Fin m) := ⟨⟨0, h.1⟩⟩
    haveI : Nonempty (Fin n) := ⟨⟨0, h.2⟩⟩
    Finset.sup' (Finset.univ (α := Fin m × Fin n))
      (Finset.univ_nonempty) (fun ij => ch.trans ij.1 ij.2)
  else 0



/-! ## Section 3: Lattice-Crypto Security Structures

We define security lattices where the partial order corresponds to
computational hardness assumptions, connecting algebraic structure
to cryptographic security. -/


/-- **Collision resistance security level**:
    A hash family with σ-bit output has at most 2^σ collision resistance.
    Bridge: connects Cryptography to InformationTheory (birthday bound).
    The birthday bound gives O(2^(σ/2)) collision complexity. -/
def collisionSecurityBits (σ : ℕ) : ℕ := σ / 2


/-- **Theorem (Post-Quantum Security Degradation)**:
    Grover's algorithm reduces collision resistance by factor of ~3 vs classical.
    Quantum collision finding: O(2^(σ/3)) vs classical O(2^(σ/2)).
    The quantum security bits are σ/3.
    Bridge: connects Cryptography to Physics (quantum computation). -/
def quantumCollisionBits (σ : ℕ) : ℕ := σ / 3



/-! ## Section 4: Entropy-Lipschitz Bridge for ML Robustness

We prove that entropy functions are Lipschitz continuous, which connects
information theory to certified robustness in machine learning. -/

/-- The L1 distance between two probability vectors.
    Bridge: connects InformationTheory to MachineLearning (robustness metrics). -/
def l1Distance {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |p i - q i|


/-- **An entropy measure with a Lipschitz constant**.
    This structure captures certified robustness: small perturbations to
    the input distribution cause bounded changes in entropy.
    Bridge: connects InformationTheory to MachineLearning (Lipschitz_bound). -/
structure LipschitzEntropyMeasure (n : ℕ) extends EntropyMeasure n where
  /-- The Lipschitz constant -/
  lipschitzConst : ℝ
  /-- Lipschitz constant is nonneg -/
  lipschitz_nonneg : 0 ≤ lipschitzConst
  /-- Lipschitz continuity: |H(p) - H(q)| ≤ L · ‖p - q‖₁ -/
  lipschitz_bound : ∀ p q : Fin n → ℝ,
    (∀ i, 0 ≤ p i) → (∀ i, 0 ≤ q i) →
    |eval p - eval q| ≤ lipschitzConst * l1Distance p q


/-! ## Section 5: Entropy Chain Rule and Decomposition

We formalize the chain rule of entropy and prove an O(n) bound on
the number of terms in the decomposition. -/

/-- A joint entropy decomposition into n conditional terms.
    The chain rule: H(X₁,...,Xₙ) = Σᵢ H(Xᵢ | X₁,...,Xᵢ₋₁).
    Bridge: connects InformationTheory (chain rule) to Algebra (decomposition theory). -/
structure EntropyChainDecomposition (n : ℕ) where
  /-- Joint entropy value -/
  jointEntropy : ℝ
  /-- Conditional entropy terms -/
  conditionalTerms : Fin n → ℝ
  /-- Each conditional term is nonneg -/
  terms_nonneg : ∀ i, 0 ≤ conditionalTerms i
  /-- Chain rule: joint = sum of conditionals -/
  chain_rule : jointEntropy = ∑ i : Fin n, conditionalTerms i




/-! ## Section 6: Tropical Entropy Encoding

We encode entropy values in the tropical semiring, showing that
information-theoretic operations correspond to tropical algebra. -/

/-- Tropical encoding of an entropy value.
    In the tropical semiring, addition becomes min and multiplication becomes +.
    Bridge: connects InformationTheory to Algebra (tropical semiring theory). -/
structure TropicalEntropy where
  /-- The entropy value in tropical encoding -/
  val : ℝ
  /-- Entropy values are nonneg -/
  nonneg : 0 ≤ val

/-- Tropical meet: takes the minimum entropy (most certain distribution).
    This corresponds to tropical addition.
    Bridge: connects Algebra (lattice meet) to InformationTheory (entropy ordering). -/
def tropicalMeet (a b : TropicalEntropy) : TropicalEntropy where
  val := min a.val b.val
  nonneg := le_min a.nonneg b.nonneg

/-- Tropical join: takes the maximum entropy (most uncertain distribution).
    Bridge: connects Algebra (lattice join) to InformationTheory. -/
def tropicalJoin (a b : TropicalEntropy) : TropicalEntropy where
  val := max a.val b.val
  nonneg := le_max_of_le_left a.nonneg





/-! ## Section 7: Key Derivation Security via Entropy Extraction

We formalize the leftover hash lemma approach to key derivation,
connecting min-entropy to cryptographic key security. -/

/-- A key derivation function parameterized by input/output entropy.
    Models the extraction of a cryptographic key from a high-entropy source.
    Bridge: connects Cryptography (key derivation) to InformationTheory (extraction). -/
structure KeyDerivation where
  /-- Min-entropy of the source (in bits) -/
  sourceEntropy : ℕ
  /-- Length of the derived key (in bits) -/
  keyLength : ℕ
  /-- Entropy loss in extraction -/
  entropyLoss : ℕ
  /-- Key length must not exceed extractable entropy -/
  feasibility : keyLength + entropyLoss ≤ sourceEntropy


/-- **Theorem (Post-Quantum Key Derivation)**:
    For post-quantum security, we need sourceEntropy ≥ 2 * keyLength + entropyLoss
    (doubling due to Grover's algorithm).
    Bridge: connects Cryptography (post_quantum_security) to Physics (quantum). -/
def postQuantumKeyDerivation (keyLen entropyLoss : ℕ) : KeyDerivation where
  sourceEntropy := 2 * keyLen + entropyLoss
  keyLength := keyLen
  entropyLoss := entropyLoss
  feasibility := by omega


/-! ## Section 8: Information-Theoretic Complexity Bounds

We establish explicit computational complexity bounds for
information-theoretic algorithms. -/

/-- Complexity class for information-theoretic computations.
    Models the number of arithmetic operations needed.
    Bridge: connects InformationTheory to Computation (complexity theory). -/
inductive ComplexityClass where
  | linear : ComplexityClass       -- O(n)
  | nLogN : ComplexityClass        -- O(n log n)
  | quadratic : ComplexityClass    -- O(n²)
  | exponential : ComplexityClass  -- O(2ⁿ)
  deriving DecidableEq

/-- Numeric encoding for complexity ordering -/
def complexityRank : ComplexityClass → ℕ
  | .linear => 0
  | .nLogN => 1
  | .quadratic => 2
  | .exponential => 3

/-- Ordering on complexity classes via rank -/
instance : LE ComplexityClass where
  le a b := complexityRank a ≤ complexityRank b

instance : DecidableRel (α := ComplexityClass) (· ≤ ·) :=
  fun a b => Nat.decLe (complexityRank a) (complexityRank b)




/-! ## Section 9: Entropy-Capacity Duality

We prove a duality between entropy and channel capacity that connects
information theory to algebraic duality theory. -/

/-- The capacity-entropy dual pair.
    For a channel with capacity C and input entropy H,
    the reliable communication rate is bounded by min(C, H).
    Bridge: connects InformationTheory (capacity) to Algebra (duality). -/
structure CapacityEntropyDual where
  /-- Channel capacity in bits -/
  capacity : ℝ
  /-- Input entropy in bits -/
  inputEntropy : ℝ
  /-- Capacity is nonneg -/
  cap_nonneg : 0 ≤ capacity
  /-- Input entropy is nonneg -/
  ent_nonneg : 0 ≤ inputEntropy

/-- The achievable rate: min of capacity and input entropy -/
def achievableRate (d : CapacityEntropyDual) : ℝ :=
  min d.capacity d.inputEntropy




/-! ## Section 10: Quantum-Classical Entropy Gap

We formalize the gap between quantum and classical entropy bounds,
connecting to post-quantum cryptographic security. -/

/-- **Quantum entropy advantage structure**:
    Models the advantage of quantum over classical information processing.
    For n qubits, quantum entropy can be up to 2n bits (Holevo bound + superdense coding).
    Bridge: connects Physics (quantum information) to Cryptography (post-quantum). -/
structure QuantumClassicalGap where
  /-- Number of qubits / classical bits -/
  numBits : ℕ
  /-- Classical entropy bound -/
  classicalBound : ℕ
  /-- Quantum entropy bound (can be up to 2× classical for superdense coding) -/
  quantumBound : ℕ
  /-- Classical bound matches number of bits -/
  classical_eq : classicalBound = numBits
  /-- Quantum bound is at most double -/
  quantum_le : quantumBound ≤ 2 * numBits



/-! ## Section 11: Entropy-Based Distinguisher Bounds

Formalize the connection between entropy difference and distinguishing
advantage, central to both information theory and cryptographic security. -/

/-- A statistical distinguisher between two distributions.
    Bridge: connects Cryptography (indistinguishability) to InformationTheory. -/
structure StatisticalDistinguisher where
  /-- Distinguishing advantage (probability of correct guess - 1/2) -/
  advantage : ℝ
  /-- Advantage is nonneg -/
  adv_nonneg : 0 ≤ advantage
  /-- Advantage is at most 1/2 (perfect distinguishing) -/
  adv_le : advantage ≤ 1 / 2




/-! ## Section 12: Lattice Cryptography Entropy Bounds

Connect lattice-based cryptographic hardness to information-theoretic bounds. -/

/-- A lattice crypto instance with dimension and modulus.
    Bridge: connects Cryptography (lattice_crypto) to Algebra (lattice theory). -/
structure LatticeCryptoInstance where
  /-- Lattice dimension -/
  dimension : ℕ
  /-- Modulus -/
  modulus : ℕ
  /-- Dimension is positive -/
  dim_pos : 0 < dimension
  /-- Modulus is at least 2 -/
  mod_ge : 2 ≤ modulus

/-- The entropy of the LWE secret: n · log₂(q) bits.
    Bridge: connects Cryptography (LWE) to InformationTheory (entropy). -/
def lweSecretEntropy (inst : LatticeCryptoInstance) : ℕ :=
  inst.dimension * Nat.log 2 inst.modulus



/-! ## Section 13: Exponential Entropy Bounds

Connect entropy to exponential growth bounds, relevant for both
cryptographic key spaces and ML model capacity. -/





end EntropyAlgebraCrypto


