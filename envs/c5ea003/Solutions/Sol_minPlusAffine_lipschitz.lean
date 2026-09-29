-- Prove2me | solution 1 for minPlusAffine_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:19:23.537725+00:00
-- url     : https://prove2.me/submissions/c8039943-72e2-4465-a5e9-18232776091c

-- Sol generated from Bridges/MinPlusVerificationCore.lean
import Mathlib
import Definitions.Def_Bridges_MinPlusVerificationCore
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Min-Plus Verification Theory: ReLU-Tropical Isomorphism and Certified Robustness

This file establishes the foundational layer of min-plus verification theory for
ReLU neural networks. The key insight is that ReLU(x) = max(0,x) is a tropical
operation in the max-plus semiring, making every ReLU network a tropical polynomial map.

## Bridge: Tropical Geometry ↔ Neural Network Verification ↔ Certified Robustness

1. **Exact verification**: The Newton fan gives the exact decision boundary geometry
2. **Polynomial-time bounds**: Lipschitz constants computable in O(kn²) time
3. **Completeness**: Min-plus certification is both sound and complete
-/

noncomputable section

open Finset BigOperators Matrix

/-! ## Section 1: Tropical Semiring Operations -/












/-! ## Section 2: ReLU as a Tropical Operation -/










/-! ## Section 3: ℓ∞ Norm for Finite Vectors -/


theorem linftyNorm_nonneg {n : ℕ} [NeZero n] (x : Fin n → ℝ) : 0 ≤ linftyNorm x := by
  unfold linftyNorm
  exact le_trans (abs_nonneg (x ⟨0, Fin.pos'⟩))
    (Finset.le_sup' (fun j => |x j|) (Finset.mem_univ ⟨0, Fin.pos'⟩))

theorem coord_le_linftyNorm {n : ℕ} [NeZero n] (x : Fin n → ℝ) (j : Fin n) :
    |x j| ≤ linftyNorm x := by
  exact Finset.le_sup' (fun j => |x j|) (Finset.mem_univ j)


/-! ## Section 4: ReLU Affine Layer -/







/-! ## Section 5: Certified Robustness -/







/-! ## Section 6: Linear Regions and Newton Fan -/






/-! ## Section 7: Tropical Deformation -/




/-! ## Section 8: Piecewise Linearity and Verification -/




/-! ## Section 9: Tropical Metric -/






/-! ## Section 10: Min-Plus Structures -/




/-! ## Section 11: Tropical Eigenvalue -/



/-! ## Section 12: Depth-Robustness -/





/-! ## Section 13: Min-Plus Fan Distance -/



/-! ## Section 14: Adversarial Examples -/



/-
**Verification completeness for linear ReLU**: within the active region,
    relu(wx+b) = wx+b.
    Bridge: connects tropical completeness ↔ exact verification.
-/

/-
**ReLU subadditivity**: relu(x+y) ≤ relu(x) + relu(y).
    Bridge: connects tropical subadditivity ↔ neural network superposition.
-/

/-
**Compositional Lipschitz power**: |f^[k](a) - f^[k](b)| ≤ L^k |a-b|.
    Bridge: connects compositional analysis ↔ depth-robustness tradeoff.
-/

/-
**Min-plus nonexpansive per coordinate**.
    Bridge: connects tropical nonexpansiveness ↔ certified robustness.
-/

/-
**Min-plus affine maps are 1-Lipschitz**.
    Bridge: connects tropical nonexpansiveness ↔ certified robustness.
-/

/-
**Fan distance implies argmin preservation**.
    Bridge: connects positive fan distance ↔ tropical robustness.
-/

/-
**Tropical deformation is 1-Lipschitz** for ε ∈ [0,1].
    Bridge: connects topological stability ↔ robust certification.
-/


theorem solution{n : ℕ} [NeZero n]
    (φ : MinPlusAffineMap n) (x y : Fin n → ℝ) :
    |φ.eval x - φ.eval y| ≤ linftyNorm (x - y) := by
  refine' abs_sub_le_iff.mpr _;
  constructor <;> rw [ MinPlusAffineMap.eval ];
  · simp +decide [ MinPlusAffineMap.eval ];
    refine' Classical.or_iff_not_imp_right.2 fun h => _;
    obtain ⟨ i, hi ⟩ := Finset.exists_mem_eq_inf' ( Finset.univ_nonempty ) ( fun i => φ.weights i + y i );
    exact ⟨ i, by cases min_cases ( Finset.univ.inf' ( Finset.univ_nonempty ) fun i => φ.weights i + y i ) φ.bias <;> linarith [ abs_le.mp ( show |x i - y i| ≤ linftyNorm ( x - y ) from coord_le_linftyNorm ( x - y ) i ) ] ⟩;
  · rw [ sub_le_iff_le_add' ];
    rw [ ← sub_le_iff_le_add ];
    refine' le_min _ _;
    · simp +decide [ linftyNorm ];
      exact fun i => Or.inl ⟨ i, by linarith [ abs_le.mp ( Finset.le_sup' ( fun j => |x j - y j| ) ( Finset.mem_univ i ) ) ] ⟩;
    · exact le_trans ( sub_le_self _ ( linftyNorm_nonneg _ ) ) ( min_le_right _ _ )
