-- Prove2me | solution 1 for BerggrenEntropy.berggren_renyi2_entropy_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:34:14.420619+00:00
-- url     : https://prove2.me/submissions/6b841d8f-98ea-4b76-b190-7af438f4f778

-- Sol generated from Bridges/BerggrenEntropyExtractor.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenEntropyExtractor

/-!
# Berggren–Entropy Extractors: Rényi-2 Randomness Amplification
  from Primitive Pythagorean Triple Orbits

This file formalizes a cryptographic/number-theoretic extractor mechanism built from
finite-depth Berggren orbits of primitive Pythagorean triples.

## Bridge: Diophantine Geometry ↔ Cryptographic Entropy Extraction

We show that the ternary branching structure of the Berggren tree—which generates
all primitive Pythagorean triples from (3,4,5)—naturally gives rise to certified
entropy sources. The key insight is that norm-shell collision bounds, derived from
the arithmetic structure of Pythagorean triples, yield Rényi-2 entropy lower bounds
that compose with the Leftover Hash Lemma for post_quantum_security applications.

## Main Results

1. Berggren transformations preserve the Pythagorean equation
2. Strict norm growth under Berggren steps
3. Positivity of all coordinates in children
4. Orbit slice cardinality bounds
5. Shell-count collision energy bounds
6. Collision probability and Rényi-2 entropy bounds
7. Certified extractor theorem (leftover hash)

## References

- Berggren (1934), Pythagorean triple trees
- Impagliazzo–Zuckerman, Leftover Hash Lemma
- Renner (2005), Rényi entropy and quantum cryptography
-/

open Finset BigOperators

noncomputable section

open BerggrenEntropy

/-! ## Section 1: Berggren Transformations on Raw Triples -/








/-! ## Section 2: Norm Growth Under Berggren Steps

We prove that the hypotenuse strictly increases under each Berggren
transformation when applied to positive Pythagorean triples. This is the key
property ensuring orbit slices are finite and entropy grows with depth. -/













/-! ## Section 3: Base Triple Certification

The root of the Berggren tree is (3, 4, 5). -/




/-! ## Section 4: Quantitative Norm Growth Bounds

Explicit lower bounds on the hypotenuse after Berggren steps,
connecting to certified_randomness_rate via entropy growth. -/



/-! ## Section 5: Orbit Slice Combinatorics -/


/-! ## Section 6: Collision Energy and Shell Counting

We develop the abstract theory of collision energy for finite sets
partitioned by an observable, then specialize to Berggren orbits. -/




/-
Bridge: Certified collision energy bound for Berggren orbits.
    The shell-count hypothesis yields an energy bound connecting
    Diophantine_geometry to information-theoretic security.

    Proof: Each shell r contributes shellCount(r)² ≤ shellCount(r) · r
    (since shellCount(r) ≤ r), and r ≤ maxNorm. Summing over shells
    and using ∑ shellCount = totalCard gives the bound.
-/
theorem collisionEnergy_le_card_mul_sup (S : ShellPartition)
    (hShell : ∀ r, S.shellCount r ≤ r) :
    S.collisionEnergy ≤ S.totalCard * S.maxNorm := by
  have h_sum_sq : S.collisionEnergy ≤ ∑ r ∈ S.shells, S.shellCount r * S.maxNorm := by
    exact Finset.sum_le_sum fun x hx => by nlinarith [ hShell x, S.shell_le_max x hx ] ;
  exact h_sum_sq.trans_eq ( by rw [ ← Finset.sum_mul, S.sum_shells ] )

/-! ## Section 7: Collision Probability and Rényi-2 Entropy -/




/-
Bridge: Collision probability is bounded by maxNorm / totalCard,
    the fundamental collision bound for certified_entropy_extraction.
-/
theorem ShellPartition.collisionProb_upper_bound (S : ShellPartition)
    (hCard : 0 < S.totalCard)
    (hShell : ∀ r, S.shellCount r ≤ r) :
    S.collisionProb ≤ (S.maxNorm : ℝ) / (S.totalCard : ℝ) := by
  unfold ShellPartition.collisionProb;
  have := collisionEnergy_le_card_mul_sup S hShell; rw [ if_neg hCard.ne' ] ; rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith;

/-! ## Section 8: Entropy Lower Bound -/

/-
Bridge: Rényi-2 entropy lower bound for Berggren orbit sources.
    The bound log(totalCard) - log(maxNorm) shows entropy grows
    with orbit depth when shells are well-spread.
    Connects Diophantine_dynamics to certified_randomness.
-/

/-! ## Section 9: Extractor Interface -/



/-! ## Section 10: Quantitative Bounds and Computational Certificates -/











/-! ## Section 11: Abstract Entropy-Extractor Composition -/



/-! ## Section 12: Depth-Dependent Entropy Estimates -/




/-! ## Section 13: Concrete Berggren Tree Computations

Explicit verification of the first two generations of the Berggren tree,
connecting abstract algebra to concrete certified_arithmetic. -/








/-! ## Section 14: Shell Statistics for Generation 1 -/



/-! ## Section 15: Ternary Branching Algebra -/





/-! ## Section 16: Real-Analytic Entropy Bounds -/




/-! ## Section 17: Thermodynamic-Diophantine Bridge

The partition function ∑ exp(-β·r) interpolates between
counting (β = 0) and ground-state selection (β → ∞). -/




/-! ## Section 18: Berggren-Entropy Extractor Profile -/






/-! ## Section 19: Shell Energy Helper Lemmas -/


/-! ## Section 20: Complete Extractor Guarantee -/







open BerggrenEntropy in
theorem solution(S : ShellPartition)
    (hCard : 1 < S.totalCard) (_hMax : 0 < S.maxNorm)
    (hShell : ∀ r, S.shellCount r ≤ r) :
    Real.log (S.totalCard : ℝ) - Real.log (S.maxNorm : ℝ) ≤ S.renyi2Entropy := by
  -- Recall that $S.renyi2Entropy = -Real.log (S.collisionProb)$.
  unfold ShellPartition.renyi2Entropy;
  split_ifs <;> simp_all +decide [ ShellPartition.collisionProb ];
  rw [ ← Real.log_mul ] <;> norm_num [ ‹¬S.totalCard = 0› ];
  · gcongr;
    · refine' mul_pos ( div_pos _ ( by positivity ) ) ( by positivity );
      -- Since $S.totalCard > 1$, there must be at least one shell with a positive count.
      obtain ⟨r, hr⟩ : ∃ r ∈ S.shells, 0 < S.shellCount r := by
        contrapose! hCard; have := S.sum_shells; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg ] ;
      exact_mod_cast Finset.single_le_sum ( fun x _ => Nat.zero_le ( S.shellCount x ^ 2 ) ) hr.1 |> lt_of_lt_of_le ( by nlinarith );
    · have := ShellPartition.collisionProb_upper_bound S ( by positivity ) hShell;
      rw [ le_div_iff₀ ] at this <;> first | positivity | simp_all +decide [ ShellPartition.collisionProb ] ;
  · contrapose! hCard; have := S.sum_shells; simp_all +decide [ ShellPartition.collisionEnergy ] ;
