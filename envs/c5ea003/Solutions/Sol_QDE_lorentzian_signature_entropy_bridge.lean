-- Prove2me | solution 1 for QDE.lorentzian_signature_entropy_bridge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:30:00.341684+00:00
-- url     : https://prove2.me/submissions/8fd8cace-af94-4fab-b054-0957ff4db686

-- Sol generated from Bridges/InformationTheory/QuantumDPPEntanglement.lean
import Mathlib
import Definitions.Def_Bridges_InformationTheory_QuantumDPPEntanglement
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Quantum DPPs and Entanglement Bounds via Lorentzian Geometry

This file formalizes the connection between determinantal point process (DPP)
generating polynomials, Lorentzian polynomial geometry, and quantum entanglement
entropy for free-fermion systems.

## Central Vision

For a positive semidefinite contraction kernel `K` (with `0 ≤ K ≤ I`), the DPP
partition polynomial `Z_K(z) = det(I + diag(z)·K)` encodes occupation statistics
of a fermionic Gaussian state. The Lorentzian geometry of `Z_K` — specifically,
the Hessian signatures of its derivative leaves — constrains the entanglement
entropy of subsystems.

## Main Definitions

* `QDE.binaryEntropy` — The function h(x) = -x log x - (1-x) log(1-x)
* `QDE.fermionicEntropyDiag` — Fermionic entropy for diagonal kernels restricted to a subset
* `QDE.principalSubmatrix` — Principal submatrix K_A for a subset A
* `QDE.twoByTwoPrincipalMinor` — The 2×2 principal minor det(K_{i,j})
* `QDE.leafCurvaturePairWitness` — Off-diagonal entry squared K_{ij}² as curvature witness
* `QDE.posIndex2x2` — Number of positive eigenvalues of a 2×2 real symmetric matrix
* `QDE.hessianPosIndexAtLeaf` — Positive index of the Hessian at a degree-2 derivative leaf
* `QDE.leafSignatureProfile` — Profile of Hessian positive indices over all pairs
* `QDE.balancedBipartitions` — Balanced bipartitions of [n]

## Main Results

* `QDE.binaryEntropy_pos` — h(x) > 0 for x ∈ (0,1)
* `QDE.fermionicEntropyDiag_mono` — Monotonicity of diagonal entropy under subset inclusion
* `QDE.diagonal_leaf_hessian_posIndex_le_one` — Degree-2 leaf Hessian has ≤ 1 pos eigenvalue
* `QDE.positive_leaf_curvature_implies_positive_entropy_pair` — Positive leaf curvature
    + strict contraction → positive 2-mode entropy
* `QDE.cauchy_schwarz_principal_minor` — Negative dependence inequality K_ij² ≤ K_ii · K_jj
-/

open Finset BigOperators Matrix Real

noncomputable section

open QDE

/-! ## §1. Core Definitions -/










/-! ## §2. Basic Properties of Binary Entropy -/




theorem binaryEntropy_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ binaryEntropy x := by
  by_cases hx : x = 0 ∨ x = 1
  · rcases hx with rfl | rfl <;> simp [binaryEntropy, Real.log_one]
  · push_neg at hx
    unfold binaryEntropy
    have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx.1)
    have h1x_pos : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx1 hx.2)
    nlinarith [Real.log_le_sub_one_of_pos hx_pos,
               Real.log_le_sub_one_of_pos h1x_pos]

/-
**Binary entropy is strictly positive on (0, 1)**: any mode with
    occupation probability strictly between 0 and 1 contributes positive entropy.
-/
theorem binaryEntropy_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < binaryEntropy x := by
  unfold binaryEntropy;
  nlinarith [ Real.log_le_sub_one_of_pos hx0, Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 - x ) ]

/-! ## §3. Diagonal Kernel Entropy -/


/-
**Monotonicity of fermionic entropy under subsystem inclusion** (diagonal case).
    Enlarging the subsystem can only increase the entropy for contraction kernels.
-/




/-
Diagonal kernel entropy is additive over disjoint subsystems.
-/

/-! ## §4. Hessian Signature at Derivative Leaves -/



/-
**Degree-2 leaf Hessian has at most 1 positive eigenvalue** (diagonal case).
    This is the concrete Lorentzian signature constraint.
-/


/-! ## §5. The Bridge: Leaf Curvature → Positive Entropy -/

/-
**Positive leaf curvature + strict contraction → positive 2-mode entropy**.

    If the degree-2 derivative leaf at `(i, j)` has nonzero curvature
    (i.e., `p i * p j > 0`), AND both modes are strictly below full
    occupation, then the fermionic entropy of the pair `{i, j}` is
    strictly positive. This turns a Hessian-signature datum into an
    entanglement bound.
-/

/-! ## §6. 2×2 Principal Submatrix Properties -/



/-
**Negative dependence as Cauchy–Schwarz**: `K_ij² ≤ K_ii · K_jj` for PSD `K`.
-/

/-! ## §7. Leaf Curvature Witness Properties -/




/-! ## §8. Explicit Family: Rank-One Projection -/



/-! ## §9. Conjectural Bridge -/

/-
**Conjecture**: If a diagonal contraction kernel has a pair with
    positive leaf curvature and strict contraction, then some balanced
    bipartition has positive entropy.
-/



open QDE in
theorem solution    {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hn : 2 ≤ n)
    (hexists : ∃ i j : Fin n, i ≠ j ∧ hessianPosIndexAtLeaf p i j = 1 ∧
               p i < 1 ∧ p j < 1) :
    ∃ A ∈ balancedBipartitions n, 0 < fermionicEntropyDiag p A := by
  -- From hexists, obtain i and j with the required properties.
  obtain ⟨i, j, hij, h_hessian, h_pi, h_pj⟩ := hexists;
  -- Since $p_i$ and $p_j$ are both in $(0,1)$, we can choose a balanced bipartition $A$ that includes $i$.
  obtain ⟨A, hA⟩ : ∃ A ∈ balancedBipartitions n, i ∈ A := by
    -- Since $n \geq 2$, we can construct a balanced bipartition $A$ that includes $i$.
    have h_exists_subset : ∃ A : Finset (Fin n), A.card = n / 2 ∧ i ∈ A := by
      -- Since $n \geq 2$, we can construct a subset $A$ of size $n/2$ that includes $i$.
      obtain ⟨A, hA⟩ : ∃ A : Finset (Fin n), A ⊆ Finset.univ \ {i} ∧ A.card = n / 2 - 1 := by
        exact Finset.exists_subset_card_eq ( by simpa [ Finset.card_sdiff ] using by omega );
      use Insert.insert i A;
      rw [ Finset.card_insert_of_notMem ( fun hi => by simpa [ hi ] using hA.1 hi ), hA.2, Nat.sub_add_cancel ( Nat.div_pos ( by linarith ) zero_lt_two ) ] ; aesop;
    exact ⟨ h_exists_subset.choose, Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ _, h_exists_subset.choose_spec.1 ⟩, h_exists_subset.choose_spec.2 ⟩;
  -- Since $p_i \in (0,1)$, we have $binaryEntropy (p_i) > 0$.
  have h_binary_entropy_pos : 0 < binaryEntropy (p i) := by
    by_cases hi : p i = 0;
    · unfold hessianPosIndexAtLeaf at h_hessian; unfold posIndex2x2 at h_hessian; aesop;
    · exact binaryEntropy_pos ( lt_of_le_of_ne ( hp i |>.1 ) ( Ne.symm hi ) ) h_pi;
  exact ⟨ A, hA.1, lt_of_lt_of_le h_binary_entropy_pos <| Finset.single_le_sum ( fun a _ => binaryEntropy_nonneg ( hp a |>.1 ) ( hp a |>.2 ) ) hA.2 ⟩
