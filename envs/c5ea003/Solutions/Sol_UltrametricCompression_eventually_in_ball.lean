-- Prove2me | solution 1 for UltrametricCompression.eventually_in_ball
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:47:39.816133+00:00
-- url     : https://prove2.me/submissions/16878599-5fa1-4489-97b6-54589287f016

-- Sol generated from Bridges/UltrametricTemporalCompression.lean
import Mathlib
import Definitions.Def_Bridges_UltrametricTemporalCompression
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
theorem iterate_dist_bound (U : UltraDist α) {S : Set α} {F : α → α} {q : NNReal}
    (hF : ContractiveOn U S F q) (n : ℕ) {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    U.dist (F^[n] x) (F^[n] y) ≤ q ^ n * U.dist x y := by
  induction' n with n ih;
  · simp +decide;
  · rw [ pow_succ', mul_assoc ];
    exact le_trans ( by simpa only [ Function.iterate_succ_apply' ] using hF.contract ( iterate_mem hF.mapsTo _ _ hx ) ( iterate_mem hF.mapsTo _ _ hy ) ) ( mul_le_mul_left' ih _ )

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
theorem iterate_to_fixedPoint_bound (U : UltraDist α) {S : Set α} {F : α → α} {q : NNReal}
    (hF : ContractiveOn U S F q) {p : α} (hp : p ∈ S) (hFp : F p = p)
    (n : ℕ) {x : α} (hx : x ∈ S) :
    U.dist (F^[n] x) p ≤ q ^ n * U.dist x p := by
  convert iterate_dist_bound U hF n hx hp using 1;
  rw [ Function.iterate_fixed hFp ]

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
    (hF : ContractiveOn U S F q) {p : α} (hp : p ∈ S) (hFp : F p = p)
    {x : α} (hx : x ∈ S) (r : NNReal) (hr : 0 < r) :
    ∃ N, ∀ n, N ≤ n → F^[n] x ∈ ultraBall U p r := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, q^N * U.dist x p < r := by
    -- Since $q < 1$, we have $q^N \to 0$ as $N \to \infty$.
    have h_q_pow_zero : Filter.Tendsto (fun N : ℕ => q^N * U.dist x p) Filter.atTop (nhds 0) := by
      convert Tendsto.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( NNReal.coe_nonneg q ) ( mod_cast hF.q_lt_one ) ) tendsto_const_nhds;
      rw [ ← NNReal.tendsto_coe ];
      congr! 1;
      norm_num;
    exact ( h_q_pow_zero.eventually ( gt_mem_nhds hr ) ) |> fun h => h.exists;
  refine' ⟨ N, fun n hn => _ ⟩;
  refine' le_trans _ hN.le;
  convert iterate_to_fixedPoint_bound U hF hp hFp n hx |> le_trans <| mul_le_mul_right' ( pow_le_pow_of_le_one ( show ( 0 : NNReal ) ≤ q by exact NNReal.coe_nonneg _ ) ( show ( q : NNReal ) ≤ 1 by exact le_of_lt hF.q_lt_one ) hn ) _ using 1;
  exact U.dist_comm _ _
