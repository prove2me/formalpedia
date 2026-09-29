-- Prove2me | solution 1 for UltrametricCompression.fixedPoint_of_complete
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:49:49.133293+00:00
-- url     : https://prove2.me/submissions/494b540a-1184-4adb-9837-047fee246815

-- Sol generated from Bridges/UltrametricTemporalCompression.lean
import Mathlib
import Definitions.Def_Bridges_UltrametricTemporalCompression
import Theorems.Thm_UltrametricCompression_orbit_cauchy
/-
Copyright (c) 2025 Harmonic. All rights reserved.

# Ultrametric Temporal Fixed-Point Compression

A formally verified theory of fixed-point compression in ultrametric proof spaces.
This establishes that iterative contractive dynamics on ultrametric spaces converge
to unique canonical compressed attractors, with quantitative bounds and algorithmic
extractors.

## Main results

* `iterate_dist_bound` — Geometric contraction bound for iterates
* `contractive_adjacent_bound` — Adjacent iterate bound
* `ultrametric_orbit_tail_bound` — Ultrametric telescoping bound
* `fixedPoint_unique` — Uniqueness of fixed points
* `orbit_cauchy` — Cauchy property of orbits
* `fixedPoint_of_complete` — Existence of fixed points in complete spaces
* `exists_unique_fixedPoint` — Existence and uniqueness combined
* `extractor_bound` — Certified extractor with quantitative error bound

## Cross-domain significance

* **Non-Archimedean dynamics**: Ultrametric contraction gives hierarchical ball stabilization
* **Proof compression**: Canonical attractors serve as compressed proof certificates
* **Reversible computation**: Invertible dynamics on compression cores yield periodic quotients
* **Temporal logic**: Convergence to fixed points = denotational semantics of temporal evolution
-/


open Function Set Filter

open UltrametricCompression

/-! ## Part 1: Ultrametric Distance Structure -/


/-! ## Part 2: Contractive and Nonexpansive Maps -/





variable {α : Type*}

/-! ## Part 3: Iterate Membership -/

/-
If F maps S to S, then F^[n] x ∈ S for all x ∈ S.
-/
theorem iterate_mem {S : Set α} {F : α → α} (hF : MapsTo F S S) :
    ∀ n x, x ∈ S → F^[n] x ∈ S := by
  exact fun n x hx => hF.iterate n hx

/-! ## Part 4: Iterate Contraction Bounds -/

/-
**Iterated contraction bound**: Under a q-contractive map on S,
n-fold iteration shrinks distances by q^n.
-/

/-
**Adjacent iterate bound**: The distance between successive iterates
decreases geometrically.
-/

/-! ## Part 5: Ultrametric Orbit Control -/

/-
**Ultrametric orbit tail bound**: In an ultrametric space, the distance
between any two iterates F^m(x) and F^n(x) (with n ≤ m) is controlled by
q^n · d(F x, x). This uses the ultrametric inequality to replace summation
with maximum, yielding a much tighter bound than in ordinary metric spaces.
-/

/-! ## Part 6: Fixed-Point Uniqueness -/

/-
**Uniqueness of fixed points**: If F is q-contractive with q < 1 on S,
then F has at most one fixed point in S.
Proof idea: d(p,p') = d(Fp, Fp') ≤ q · d(p,p'), and q < 1 forces d(p,p') = 0.
-/

/-! ## Part 7: Cauchy Orbits -/

/-
**Cauchy orbits**: Under contraction, orbits are Cauchy sequences
in the sense that tail differences become arbitrarily small.
-/

/-! ## Part 8: Fixed-Point Existence (with Completeness) -/


/-
**Fixed-point existence**: In a complete ultrametric space, a contractive
map on a nonempty invariant set has a fixed point, and all orbits converge to it.
-/

/-
**Existence and uniqueness combined**: The ultrametric Banach fixed-point theorem.
In a nonempty complete invariant region, a contractive map has exactly one fixed point.
-/

/-! ## Part 9: Quantitative Convergence to Fixed Point -/

/-
**Quantitative convergence**: Distance from F^n(x) to the fixed point
satisfies d(F^n x, p) ≤ q^n · d(x, p).
-/

/-! ## Part 10: Certified Extractor -/


/-
**Extractor error bound with nonexpansive compression**:
The compressed extractor output is within q^N · d(x, p⋆) of the fixed point,
provided C is nonexpansive and fixes p⋆.
-/

/-! ## Part 11: Compression Core Stability -/


/-
**Compression core stability**: If C is idempotent and p⋆ = C(T(p⋆)),
then C(p⋆) = p⋆. The fixed point is in the image of C, i.e., it is
already a compressed representative.
-/

/-! ## Part 12: Ultrametric Isosceles Lemma -/

/-
**Isosceles lemma**: In an ultrametric space, if d(x,y) < d(y,z),
then d(x,z) = d(y,z). Every ultrametric triangle is isosceles with
the unequal side being the shortest.
-/

/-! ## Part 13: Ball Stabilization -/


/-
Under contraction, iterates eventually enter any ball around
the fixed point.
-/

/-! ## Part 14: Composition Theorems -/




open UltrametricCompression in
theorem solution(U : UltraDist α) {S : Set α} {F : α → α} {q : NNReal}
    (hF : ContractiveOn U S F q) (hS : S.Nonempty)
    (hComplete : IsComplete' U S) :
    ∃ p ∈ S, F p = p ∧
      ∀ x ∈ S, ∀ ε : NNReal, 0 < ε →
        ∃ N, ∀ n, N ≤ n → U.dist (F^[n] x) p < ε := by
  obtain ⟨ p, hp ⟩ := hComplete.complete ( fun n => F^[n] hS.some ) ( fun n => iterate_mem hF.mapsTo _ _ hS.choose_spec ) ( orbit_cauchy U hF hS.choose_spec );
  -- Show that $F(p) = p$.
  have hFp : F p = p := by
    -- By the properties of the ultrametric distance and the contraction property, we have that the distance between F(p) and p is less than or equal to q times the distance between p and F^[N] hS.some.
    have h_dist_Fp_p : ∀ ε > 0, ∃ N, ∀ n ≥ N, U.dist (F p) p ≤ max (q * U.dist p (F^[n] hS.some)) (U.dist (F^[n+1] hS.some) p) := by
      intro ε hε
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, U.dist (F p) (F^[n+1] hS.some) ≤ q * U.dist p (F^[n] hS.some) := by
        have := hF.contract;
        exact ⟨ 0, fun n hn => by simpa only [ Function.iterate_succ_apply' ] using this hp.1 ( iterate_mem hF.mapsTo _ _ hS.choose_spec ) ⟩;
      exact ⟨ N, fun n hn => le_trans ( U.dist_ultra _ _ _ ) ( max_le_max ( hN n hn ) le_rfl ) ⟩;
    -- Since $q < 1$, we have that $q * U.dist p (F^[n] hS.some) \to 0$ as $n \to \infty$.
    have h_q_dist_zero : Filter.Tendsto (fun n => q * U.dist p (F^[n] hS.some)) Filter.atTop (nhds 0) := by
      have h_q_dist_zero : Filter.Tendsto (fun n => U.dist p (F^[n] hS.some)) Filter.atTop (nhds 0) := by
        rw [ Metric.tendsto_nhds ];
        simp_all +decide [ dist_comm, U.dist_comm ];
        exact fun ε hε => by rcases hp.2 ⟨ ε, hε.le ⟩ hε with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => by simpa [ NNReal.dist_eq ] using hN n hn ⟩ ;
      simpa using h_q_dist_zero.const_mul q;
    -- Since $U.dist (F^[n+1] hS.some) p \to 0$ as $n \to \infty$, we have that $max (q * U.dist p (F^[n] hS.some)) (U.dist (F^[n+1] hS.some) p) \to 0$.
    have h_max_zero : Filter.Tendsto (fun n => max (q * U.dist p (F^[n] hS.some)) (U.dist (F^[n+1] hS.some) p)) Filter.atTop (nhds 0) := by
      have h_dist_zero : Filter.Tendsto (fun n => U.dist (F^[n+1] hS.some) p) Filter.atTop (nhds 0) := by
        exact tendsto_order.2 ⟨ fun ε => by aesop, fun ε hε => by rcases hp.2 ε hε with ⟨ N, hN ⟩ ; exact Filter.eventually_atTop.2 ⟨ N, fun n hn => hN _ ( Nat.le_succ_of_le hn ) ⟩ ⟩;
      simpa using Filter.Tendsto.max h_q_dist_zero h_dist_zero;
    have h_dist_Fp_p_zero : U.dist (F p) p = 0 := by
      exact le_antisymm ( le_of_tendsto_of_tendsto tendsto_const_nhds h_max_zero ( Filter.eventually_atTop.mpr ( h_dist_Fp_p 1 zero_lt_one ) ) ) ( NNReal.coe_nonneg _ );
    grind +suggestions;
  refine' ⟨ p, hp.1, hFp, fun x hx ε hε => _ ⟩;
  -- By the properties of the ultrametric space and the contraction mapping, we have that $U.dist (F^[n] x) p \leq q^n * U.dist x p$.
  have h_dist : ∀ n, U.dist (F^[n] x) p ≤ q^n * U.dist x p := by
    intro n;
    induction' n with n ih;
    · simp +decide;
    · have := hF.contract ( show F^[n] x ∈ S from ?_ ) ( show p ∈ S from hp.1 );
      · simpa only [ hFp, pow_succ', mul_assoc, Function.iterate_succ_apply' ] using this.trans ( mul_le_mul_left' ih _ );
      · exact iterate_mem hF.mapsTo n x hx;
  -- Since $q < 1$, we have that $q^n \to 0$ as $n \to \infty$.
  have h_q_pow_zero : Filter.Tendsto (fun n => q^n * U.dist x p) Filter.atTop (nhds 0) := by
    have h_q_pow_zero : Filter.Tendsto (fun n => q^n) Filter.atTop (nhds 0) := by
      simpa using tendsto_pow_atTop_nhds_zero_of_lt_one ( NNReal.coe_nonneg q ) hF.q_lt_one;
    simpa using h_q_pow_zero.mul tendsto_const_nhds;
  exact Filter.eventually_atTop.mp ( h_q_pow_zero.eventually ( gt_mem_nhds hε ) ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn => lt_of_le_of_lt ( h_dist n ) ( hN n hn ) ⟩
