-- Prove2me | solution 1 for trace_power_abs_bound_rowSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:26:27.461406+00:00
-- url     : https://prove2.me/submissions/2e811cef-158b-4df4-a43f-9c09f0331e50

-- Sol generated from Bridges/RuelleTransferSemantics.lean
import Mathlib
import Definitions.Def_Bridges_RuelleTransferSemantics
/-
  # Algebra–EML Ruelle Transfer Semantics via Closure Correspondence Operators
  # and Artin–Mazur Rationality

  This file develops a finite-dimensional bridge between algebraic dynamics,
  EML observable semantics, symbolic zeta theory, and transfer operator spectral
  theory. The central construction associates to each finite dynamical system
  a correspondence matrix whose trace powers count periodic orbits, yielding
  rationality of the Artin–Mazur zeta function from finite-rank operator data.

  ## Cross-Domain Bridges

  - **Algebraic dynamics ↔ EML closure semantics**: closure-stable observable bases
  - **Symbolic zeta theory ↔ finite quantum transfer operators**: trace = periodic count
  - **Certified robustness ↔ transfer-operator norms**: row-sum Lipschitz bounds
  - **Lattice crypto ↔ periodic orbit counting**: transition kernel recurrences
  - **Hamiltonian/thermodynamic ↔ weighted correspondence**: loop sum expansion
-/


open scoped BigOperators Matrix
open Finset Function Matrix

/-! ## Part 1: Core Structures and Definitions -/





















/-! ## Part 2: Periodic Point Theorems -/




/-
Periodic point counts are invariant under conjugacy.
    Bridge: connects dynamical conjugacy to post_quantum_security state-isomorphism auditing.

    This is a fundamental symmetry: if two dynamical systems are conjugate via an equivalence,
    they have the same periodic orbit structure at every period.
-/

/-! ## Part 3: Observable Basis and Pullback Matrix -/



/-! ## Part 4: Weighted Loop Sums and Trace Identity -/




/-! ## Part 5: Deterministic Correspondence -/


/-
Powers of the deterministic correspondence matrix count iterate-based reachability.
    `(M^n) x y = if f^[n] x = y then 1 else 0`.
    Bridge: connects symbolic dynamics iterate structure to matrix power combinatorics.
-/

/-
**Flagship trace theorem**: For a deterministic dynamical system, the trace of the
    correspondence matrix power equals the periodic point count.
    Bridge: connects algebraic dynamics to EML trace semantics — the discrete Lefschetz formula.

    This is the central identity `tr(M^n) = |Fix(f^n)|` that underlies
    Artin–Mazur zeta rationality and connects to quantum_entropy orbit counting.
-/

/-! ## Part 6: Norm Bounds and Certified Robustness -/

/-
Row-sum norm is nonneg.
    Bridge: connects certified_robustness norm positivity to transfer operator theory.
-/
theorem rowSumNorm_nonneg
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℚ) :
    0 ≤ rowSumNorm M := by
  unfold rowSumNorm;
  induction' ( Finset.univ : Finset ι ) using Finset.induction with x s hx ih;
  exact Rat.le_refl
  simp +decide [*];
  · exact Or.inl ( add_nonneg ( abs_nonneg _ ) ( Finset.sum_nonneg fun _ _ => abs_nonneg _ ) );
  · exact Classical.decEq ι

/-
Sup-norm is nonneg.
-/

/-
The matrix-vector product is bounded by the row-sum norm times the vector sup-norm.
    Bridge: connects certified_robustness Lipschitz bounds to transfer-operator norm theory.

    `‖Lv‖∞ ≤ rowSumNorm(L) · ‖v‖∞` — finite-dimensional Lipschitz property.
-/

/-
The trace of a matrix power is bounded by `card β * rowSumNorm(L)^n`.
    Bridge: connects certified_robustness_rowSum to Ruelle transfer growth control.
-/



/-
The Artin–Mazur coefficient is bounded by the state space cardinality.
    Bridge: connects lattice_crypto orbit collision bounds to finite zeta coefficient control.
-/

/-! ## Part 7: Observable Trace Matching -/


/-
Observable trace controls periodic growth via the pullback row-sum norm.
    Bridge: connects hamiltonian_entropy observable bounds to certified_robustness.
-/

/-
Weighted loop sums are nonneg when all weights are nonneg.
    Bridge: connects thermodynamic positivity (partition function) to certified transfer bounds.
-/

/-! ## Part 8: The Flagship Rationality Theorem -/


theorem solution    {β : Type*} [Fintype β] [DecidableEq β]
    (L : Matrix β β ℚ) :
    ∀ n : ℕ,
      |matrixTracePow L n| ≤ (Fintype.card β : ℚ) * (rowSumNorm L) ^ n := by
  -- By induction on $n$, we can show that $|(L^n)_{ij}| \leq (\text{rowSumNorm } L)^n$ for all $i, j$.
  have h_ind : ∀ n : ℕ, ∀ i j : β, |(L ^ n) i j| ≤ (rowSumNorm L) ^ n := by
    intro n i j;
    induction' n with n ih generalizing i j <;> simp_all +decide [ pow_succ', Matrix.mul_apply ];
    · by_cases hij : i = j <;> aesop;
    · refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
      simp +decide only [abs_mul];
      refine' le_trans ( Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ( ih x j ) ( abs_nonneg _ ) ) _;
      rw [ ← Finset.sum_mul _ _ _ ];
      refine' mul_le_mul_of_nonneg_right _ ( pow_nonneg ( rowSumNorm_nonneg L ) _ );
      have h_fold_max : ∀ (s : Finset β) (f : β → ℚ), (∀ i ∈ s, f i ≤ Finset.fold max 0 f s) := by
        intro s f i hi; induction s using Finset.induction <;> aesop;
      exact h_fold_max _ _ _ ( Finset.mem_univ _ );
  intro n;
  exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum fun i _ => h_ind n i i ) ( by simp +decide [ mul_comm ] ) )
