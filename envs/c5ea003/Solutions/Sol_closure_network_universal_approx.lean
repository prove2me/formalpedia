-- Prove2me | solution 1 for closure_network_universal_approx
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:50:34.665928+00:00
-- url     : https://prove2.me/submissions/cb9f032b-a005-44a3-b6e8-c1f7da3281d5

-- Sol generated from MachineLearning/HilbertSpace/ClosureNetworkBreakthrough.lean
import Mathlib
import Definitions.Def_MachineLearning_HilbertSpace_ClosureNetworkBreakthrough
/-
  # Closure-Operator Networks: Universal Approximation via Idempotent Semimodules
  # — Breakthrough Theorem Package

  This file establishes that closure-operator networks are algebraically natural
  universal approximators with built-in certification:

  ## Theorem A — Universal Approximation on Compact Domains
  Every continuous function on a compact subset of ℝⁿ is uniformly approximable
  by a finite closure-operator network to arbitrary precision.

  ## Theorem B — Rate Comparison with Piecewise-Affine/ReLU Approximation
  If a function admits uniform piecewise-affine approximation, then it admits
  closure-network approximation at the same rate — closure networks are competitive.

  ## Theorem C — Certified Robustness from Closure Geometry
  Closure networks with radius structure are certifiably robust: perturbations
  within the closure radius preserve predictions. Combined with approximation
  under margin, this yields robust classification transfer.

  The package demonstrates that closure-operator networks are not merely universal
  approximators, but form an algebraically natural framework where expressivity,
  approximation rate, and robustness certification are unified.
-/

open Set Function Finset Classical Metric Filter

noncomputable section

/-! ## Part 1: Definitions -/





/-! ## Part 2: Helper Lemmas -/

/-
Compact sets in pseudometric spaces admit finite ε-nets.
-/
theorem compact_finite_eps_net
    {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K) :
    ∀ ε > 0, ∃ S : Finset X,
      (↑S ⊆ K) ∧
      ∀ x ∈ K, ∃ s ∈ S, dist x s < ε := by
        intro ε hε;
        have := hK.elim_nhds_subcover;
        exact Exists.elim ( this ( fun x => Metric.ball x ε ) fun x hx => Metric.ball_mem_nhds x hε ) fun t ht => ⟨ t, ht.1, fun x hx => by simpa using ht.2 hx ⟩

/-
Continuous functions on compact sets are uniformly continuous (ε-δ form).
-/
theorem uniformContinuousOn_compact_of_continuous
    {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K)
    (f : X → ℝ) (hf : ContinuousOn f K) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → |f x - f y| < ε := by
      exact fun ε ε_pos => by rcases Metric.uniformContinuousOn_iff.mp ( hK.uniformContinuousOn_of_continuous hf ) ε ε_pos with ⟨ δ, δ_pos, hδ ⟩ ; exact ⟨ δ, δ_pos, fun x hx y hy hxy => hδ x hx y hy hxy ⟩ ;

/-
Uniform approximation preserves sign under margin.
-/

/-! ## Part 3: Theorem A — Universal Approximation on Compact Domains -/

/-
**Theorem A (General): Universal approximation by finite closure networks
    on compact pseudometric spaces.**

    Every continuous function on a compact set in a pseudometric space
    can be uniformly approximated to arbitrary precision by a function
    with finite range (a finite closure network).

    **Proof strategy**: Use uniform continuity on the compact set to get δ,
    extract a finite δ-net from compactness, and build a nearest-neighbor
    codebook approximant. The codebook function takes finitely many values
    (one per net point), giving a finite closure network.
-/



/-! ## Part 4: Theorem B — Rate Comparison -/


/-! ## Part 5: Theorem C — Certified Robustness -/




/-
**Corollary: Combined approximation + robustness.**

    A closure network that approximates a function with margin also
    certifies that the sign is robust within its local constancy radius.
-/

/-! ## Part 6: Algebraic Structure -/


/-
Composition of commuting idempotent monotone functions is idempotent and monotone.
-/

/-
ReLU is an idempotent, monotone, extensive function — a closure operator on ℝ.
-/

/-! ## Part 7: Lipschitz Rate Theorem -/

/-
**Lipschitz Error Bound**: For Lipschitz functions, closure-network
    approximation error decays linearly with covering radius.
-/


theorem solution    {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K)
    (f : X → ℝ) (hf : ContinuousOn f K) :
    ∀ ε > 0, ∃ N : X → ℝ,
      IsFiniteClosureNetwork N ∧
      ∀ x ∈ K, |N x - f x| < ε := by
        intro ε εpos;
        -- Use uniform continuity on the compact set to get δ > 0 such that for x, y ∈ K with dist x y < δ, |f x - f y| < ε.
        obtain ⟨δ, δpos, hδ⟩ : ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → |f x - f y| < ε := by
          exact uniformContinuousOn_compact_of_continuous hK f hf ε εpos
        -- Use compact_finite_eps_net with δ to get a finite set S ⊆ K covering K.
        obtain ⟨S, hS_sub, hS_cover⟩ : ∃ S : Finset X, (↑S ⊆ K) ∧ ∀ x ∈ K, ∃ s ∈ S, dist x s < δ := by
          exact compact_finite_eps_net hK δ δpos
        refine' ⟨ fun x => if hx : x ∈ K then f ( Classical.choose ( hS_cover x hx ) ) else 0, _, _ ⟩;
        · refine' ⟨ Set.Finite.subset ( Set.toFinite ( Finset.image f S ∪ { 0 } ) ) _ ⟩;
          grind;
        · intro x hx; specialize hδ x hx ( Classical.choose ( hS_cover x hx ) ) ( hS_sub ( Classical.choose_spec ( hS_cover x hx ) |>.1 ) ) ( Classical.choose_spec ( hS_cover x hx ) |>.2 ) ; simp_all +decide [ abs_sub_comm ] ;
