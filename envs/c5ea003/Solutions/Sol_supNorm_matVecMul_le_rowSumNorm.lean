-- Prove2me | solution 1 for supNorm_matVecMul_le_rowSumNorm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:26:17.272659+00:00
-- url     : https://prove2.me/submissions/8fb678ed-22f9-4f60-bb07-f7ff43cb232f

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
theorem supNorm_nonneg {β : Type*} [Fintype β] (v : β → ℚ) :
    0 ≤ supNorm v := by
  -- The absolute value of any real number is nonnegative for the order relation $\geq$ on $\mathbb{R}$. Therefore the result under a monotonic supremum operation remains nonnegative.
  have h_abs_geq : ∀ x : β, 0 ≤ |v x| := by
    exact fun x => abs_nonneg _;
  -- For any function type $\beta \rightarrow \mathbb{Q}$, `Finset.univ.fold max 0` computes the maximum of all `|v x|` values.
  -- Since every `|v x|` is $\geq 0$, `max` of nonneg values $\geq 0$, yielding the desired result.
  have h_sup_geq : (Finset.univ : (Finset β)).fold max 0 (fun i => |v i|) ≥ 0 := by
    induction' ( Finset.univ : Finset β ) using Finset.induction <;> simp_all +decide;
    apply Classical.decEq
  exact h_sup_geq

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
    (L : Matrix β β ℚ) (v : β → ℚ) :
    supNorm (matVecMul L v) ≤ rowSumNorm L * supNorm v := by
  -- We'll use the fact that if the norm of each component of a vector is bounded by some value, then the norm of the vector itself is also bounded by that value.
  have h_bound : ∀ i, |matVecMul L v i| ≤ (∑ j, |L i j|) * supNorm v := by
    intro i
    have h_abs : |matVecMul L v i| ≤ ∑ j, |L i j| * |v j| := by
      simpa only [ ← abs_mul, matVecMul ] using Finset.abs_sum_le_sum_abs _ _;
    rw [ Finset.sum_mul _ _ _ ];
    refine' le_trans h_abs ( Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left _ ( abs_nonneg _ ) );
    unfold supNorm;
    grind +suggestions;
  have h_max_bound : ∀ i, |matVecMul L v i| ≤ rowSumNorm L * supNorm v := by
    intro i
    have h_max_bound_i : (∑ j, |L i j|) ≤ rowSumNorm L := by
      have h_max_bound_i : ∀ (s : Finset β) (f : β → ℚ), ∀ i ∈ s, f i ≤ Finset.fold Max.max 0 f s := by
        intro s f i hi; induction s using Finset.induction <;> aesop;
      exact h_max_bound_i _ _ _ ( Finset.mem_univ _ )
    exact le_trans (h_bound i) (mul_le_mul_of_nonneg_right h_max_bound_i (supNorm_nonneg v));
  have h_fold_le : ∀ {s : Finset β} {f : β → ℚ}, (∀ i ∈ s, f i ≤ rowSumNorm L * fold max 0 (fun i => |v i|) univ) → fold max 0 f s ≤ rowSumNorm L * fold max 0 (fun i => |v i|) univ := by
    intros s f hf; induction s using Finset.induction <;> simp_all +decide [ Finset.fold ] ;
    exact mul_nonneg ( rowSumNorm_nonneg L ) ( by induction' ( Finset.univ : Finset β ) using Finset.induction <;> aesop );
  exact h_fold_le fun i _ => h_max_bound i
