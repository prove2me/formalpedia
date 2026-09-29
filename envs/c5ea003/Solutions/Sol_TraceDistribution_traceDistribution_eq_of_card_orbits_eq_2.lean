-- Prove2me | solution 2 for TraceDistribution.traceDistribution_eq_of_card_orbits_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:59:32.380162+00:00
-- url     : https://prove2.me/submissions/241e65d3-2ea0-4aa4-88fb-5052bcd34941

import Mathlib
import Definitions.Def_Logic_TraceDistribution_Core

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Logic/TraceDistribution/PowerSums.lean ====
/-
# Power-sum rigidity for multisets of naturals

This file develops the purely combinatorial engine behind the *trace distribution*
theorem for finite group actions (`Logic.TraceDistribution.Core`).

The key statement is `multiset_eq_of_powerSum_eq_of_support`: a multiset of natural
numbers is completely determined by its first `n` power sums `p_k = ∑_{a ∈ A} a^k`,
`k < n`, as soon as `n` is at least the number of *distinct* values occurring in the
two multisets being compared.  Two convenient specialisations follow:

* `multiset_eq_of_powerSum_eq` — the value-bound form: if every element is `< n`, the
  power sums `p_0, …, p_{n-1}` determine the multiset;
* the support form is strictly stronger and is what gives the group-theoretic bound
  `2·|G|` in `Core`, independent of the size of the set being acted on.

The proof is a *Lagrange-interpolation duality* argument, not a Newton-identity
argument, and therefore never needs the two multisets to have equal cardinality
(the `k = 0` power sum records the cardinality automatically):

* `vanishing_of_power_sums` — if a `ℚ`-valued "signed measure" `c` supported on a
  finite set of `≤ n` distinct nodes annihilates every monomial `x^k`, `k < n`, then
  it annihilates every polynomial of degree `< n`, in particular the Lagrange basis
  polynomials, hence `c = 0`.
* `powerSum_cast_of_subset` — the bookkeeping identity rewriting a multiset power sum
  as a multiplicity-weighted sum over any finite set containing the multiset.

## Lab notes (experimental data)

Numerical checks performed while fixing the statement (see `ComputationalEvidence.md`):

* `A = {1,4}`, `B = {2,3}`: `p_0` agrees (`2 = 2`), `p_1` agrees (`5 = 5`), `p_2` does
  not (`17 ≠ 13`).  Support size is `4`, and indeed `k ≤ 1` is not enough.
* `A = {0,1,2}`, `B = {0,0,3}`: `p_0 = 3 = p_0`, `p_1 = 3 = p_1`, `p_2 = 5 ≠ 9`.
* The threshold is *exactly* optimal: `Logic.TraceDistribution.Sharpness` constructs,
  for every `n`, multisets `A ≠ B` with all values `≤ n` whose power sums agree for
  every `k < n` (the alternating binomial / `n`-th finite difference measure).
-/

open Finset Polynomial

namespace TraceDistribution

/-- **Interpolation duality.**  Let `v : ι → ℚ` be injective on a finite set `S` with
`#S ≤ n`, and let `c : ι → ℚ` be arbitrary.  If the "moments"
`∑ i ∈ S, c i * (v i)^k` vanish for every `k < n`, then `c` vanishes on `S`.

The proof pairs the moment hypothesis against the Lagrange basis polynomial at each
node: it has degree `#S - 1 < n`, so it is a `ℚ`-combination of monomials that are
already known to be annihilated, while it evaluates to the Kronecker delta at the
nodes. -/
theorem vanishing_of_power_sums {ι : Type*} [DecidableEq ι] {S : Finset ι} {v : ι → ℚ}
    (hv : Set.InjOn v (S : Set ι)) {c : ι → ℚ} {n : ℕ} (hcard : S.card ≤ n)
    (h : ∀ k < n, ∑ i ∈ S, c i * (v i) ^ k = 0) : ∀ i ∈ S, c i = 0 := by
  intro w hw
  set P : ℚ[X] := Lagrange.basis S v w with hP
  have hdeg : P.natDegree < n := by
    rw [hP, Lagrange.natDegree_basis hv hw]
    have : 1 ≤ S.card := Finset.card_pos.mpr ⟨w, hw⟩
    omega
  -- Pairing `c` against the Lagrange basis polynomial at `w` isolates `c w`.
  have key : ∑ i ∈ S, c i * P.eval (v i) = c w := by
    rw [Finset.sum_eq_single w]
    · rw [Lagrange.eval_basis_self hv hw, mul_one]
    · intro b hb hbw
      rw [Lagrange.eval_basis_of_ne (Ne.symm hbw) hb, mul_zero]
    · intro hnw; exact absurd hw hnw
  have step : ∀ i ∈ S, c i * P.eval (v i) = ∑ k ∈ range n, c i * (P.coeff k * (v i) ^ k) := by
    intro i _
    rw [Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum]
  -- ... but the same pairing is a finite combination of the vanishing moments.
  have expand : ∑ i ∈ S, c i * P.eval (v i)
      = ∑ k ∈ range n, P.coeff k * (∑ i ∈ S, c i * (v i) ^ k) := by
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [← key, expand]
  exact Finset.sum_eq_zero fun k hk => by rw [h k (Finset.mem_range.mp hk), mul_zero]

/-- Rewriting a multiset power sum as a multiplicity-weighted sum over any finite set
containing the multiset. -/
theorem powerSum_cast_of_subset (A : Multiset ℕ) (S : Finset ℕ) (hA : ∀ a ∈ A, a ∈ S) (k : ℕ) :
    (((Multiset.map (fun a => a ^ k) A).sum : ℕ) : ℚ)
      = ∑ m ∈ S, (A.count m : ℚ) * (m : ℚ) ^ k := by
  classical
  have h1 : ((Multiset.map (fun a => a ^ k) A).sum : ℕ) = ∑ m ∈ A.toFinset, A.count m * m ^ k :=
    Finset.sum_multiset_map_count A (fun a => a ^ k)
  have h2 : ∑ m ∈ A.toFinset, ((A.count m : ℚ) * (m : ℚ) ^ k)
      = ∑ m ∈ S, ((A.count m : ℚ) * (m : ℚ) ^ k) := by
    refine Finset.sum_subset (fun x hx => hA x (Multiset.mem_toFinset.mp hx)) (fun x _ hx => ?_)
    simp [Multiset.count_eq_zero_of_notMem (fun hh => hx (Multiset.mem_toFinset.mpr hh))]
  rw [h1, ← h2]
  push_cast
  ring

/-- **Support form of power-sum rigidity.**  If the joint support of `A` and `B` has at
most `n` distinct values and the power sums `p_k` agree for all `k < n`, then `A = B`.

Note that `k = 0` is included, which is exactly what forces `A` and `B` to have the
same cardinality; no equal-cardinality hypothesis is needed. -/
theorem multiset_eq_of_powerSum_eq_of_support {A B : Multiset ℕ} {n : ℕ}
    (hcard : (A + B).toFinset.card ≤ n)
    (h : ∀ k < n, (Multiset.map (fun a => a ^ k) A).sum
      = (Multiset.map (fun a => a ^ k) B).sum) : A = B := by
  classical
  set S := (A + B).toFinset with hS
  have hAS : ∀ a ∈ A, a ∈ S := fun a ha =>
    Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inl ha))
  have hBS : ∀ b ∈ B, b ∈ S := fun b hb =>
    Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inr hb))
  have hvan : ∀ m ∈ S, ((A.count m : ℚ) - (B.count m : ℚ)) = 0 := by
    refine vanishing_of_power_sums (v := fun m : ℕ => (m : ℚ)) (n := n)
      Nat.cast_injective.injOn hcard ?_
    intro k hk
    have hh : ∀ m ∈ S, ((A.count m : ℚ) - (B.count m : ℚ)) * (m : ℚ) ^ k
        = (A.count m : ℚ) * (m : ℚ) ^ k - (B.count m : ℚ) * (m : ℚ) ^ k := fun m _ => by ring
    rw [Finset.sum_congr rfl hh, Finset.sum_sub_distrib,
      ← powerSum_cast_of_subset A S hAS k, ← powerSum_cast_of_subset B S hBS k, h k hk, sub_self]
  ext m
  by_cases hm : m ∈ S
  · have h1 := hvan m hm
    have h2 : (A.count m : ℚ) = (B.count m : ℚ) := by linarith
    exact_mod_cast h2
  · rw [Multiset.count_eq_zero_of_notMem (fun hh => hm (hAS m hh)),
      Multiset.count_eq_zero_of_notMem (fun hh => hm (hBS m hh))]

/-- **Value-bound form of power-sum rigidity.**  If every element of `A` and of `B` is
`< n`, and the power sums agree for all `k < n`, then `A = B`. -/
theorem multiset_eq_of_powerSum_eq {A B : Multiset ℕ} {n : ℕ}
    (hA : ∀ a ∈ A, a < n) (hB : ∀ b ∈ B, b < n)
    (h : ∀ k < n, (Multiset.map (fun a => a ^ k) A).sum
      = (Multiset.map (fun a => a ^ k) B).sum) : A = B := by
  classical
  refine multiset_eq_of_powerSum_eq_of_support ?_ h
  calc (A + B).toFinset.card ≤ (Finset.range n).card := by
        refine Finset.card_le_card fun x hx => ?_
        rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hx) with hx' | hx'
        · exact Finset.mem_range.mpr (hA x hx')
        · exact Finset.mem_range.mpr (hB x hx')
    _ = n := Finset.card_range n

end TraceDistribution
-- ==== upstream: Packages/Catalog/Logic/TraceDistribution/Core.lean ====
/-
# Conjecture A, closed: trace distributions of finite group actions

Let `G` be a finite group acting on a finite set `X`.  Two invariants compete for the
role of "the" combinatorial shadow of the action:

* the **trace distribution** `traceDistribution G X = {| X^g | : g ∈ G}`, the multiset
  of fixed-point counts (equivalently, the permutation character of the action, taken
  as an unordered multiset rather than as a class function);
* the **orbit spectrum** `k ↦ orbitCount G X k`, the number of `G`-orbits on the set
  `X^k` of `k`-tuples (`Fin k → X`).

The main results of this file prove that the two invariants are *equivalent*, and that
the equivalence is already witnessed by a finite, explicitly bounded, range of `k`:

* `orbitCount_mul_card_group` — Burnside's lemma in the graded form
  `|orbits on X^k| · |G| = ∑_{g ∈ G} |X^g|^k`, i.e. the orbit spectrum is exactly the
  sequence of **power sums** of the trace distribution.
* `traceDistribution_eq_iff_card_orbits_eq` — **the main theorem.** Two actions have
  the same trace distribution **iff** they have the same orbit counts on `k`-tuples
  for all `k ≤ max (|X|) (|Y|)`.
* `card_orbits_eq_of_le` — the finite range of `k` already forces agreement for
  *every* `k`: the orbit spectrum is a *rigid* sequence.
* `traceDistribution_graded_eq` — the gradewise q-series form: the fixed-point
  generating polynomial `∑_{g ∈ G} q^{|X^g|} ∈ ℤ[q]` is a complete invariant, and it
  agrees for `X` and `Y` iff the finitely many orbit counts do.

The bridge from "equal power sums" to "equal multisets" is `multiset_eq_of_powerSum_eq`,
proved in `Logic.TraceDistribution.PowerSums` by Lagrange-interpolation duality.

## Lab notes (experimental data)

* `G = ℤ/2` acting on `X = ℤ/2` by translation: `traceDistribution = {2, 0}`,
  orbit counts `1, 1, 2, 4, 8, …` (`= (2^k + 0^k)/2`).
* `G = ℤ/2` acting trivially on a 1-point set `Y`: `traceDistribution = {1, 1}`,
  orbit counts `1, 1, 1, 1, …`.  The two are separated already at `k = 2`
  (`2 ≠ 1`), well inside the bound `max(2,1) = 2`.
* The bound is *not* vacuous: `k = 0` always gives `orbitCount = 1` for both actions
  and `k = 1` gives the plain orbit count, so genuinely higher `k` is needed.
-/


open MulAction Finset

namespace TraceDistribution

/-! ## Definitions -/

-- [dropped: platform already declares fixedCard]
-- [dropped: platform already declares traceDistribution]
-- [dropped: platform already declares orbitCount]
-- [dropped: platform already declares traceSeries]
/-- Burnside's lemma in `Nat.card` form. -/
theorem burnside (G : Type*) [Group G] [Fintype G] (β : Type*) [MulAction G β] [Finite β] :
    ∑ g : G, fixedCard β g = Nat.card (Quotient (orbitRel G β)) * Nat.card G := by
  classical
  have _ := Fintype.ofFinite β
  have _ := Fintype.ofFinite (Quotient (orbitRel G β))
  simp only [fixedCard, Nat.card_eq_fintype_card]
  exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G β

-- [dropped: platform already declares fixedByPiEquiv]
/-- `|(X^k)^g| = |X^g|^k`. -/
theorem fixedCard_pi {G : Type*} [Group G] (X : Type*) [MulAction G X] [Finite X]
    (g : G) (k : ℕ) : fixedCard (Fin k → X) g = (fixedCard X g) ^ k := by
  unfold fixedCard
  rw [Nat.card_congr (fixedByPiEquiv X g k)]
  simp [Nat.card_pi]

theorem powerSum_traceDistribution (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] (k : ℕ) :
    (Multiset.map (fun a => a ^ k) (traceDistribution G X)).sum
      = ∑ g : G, (fixedCard X g) ^ k := by
  rw [traceDistribution, Multiset.map_map]
  rfl

/-- **Graded Burnside lemma.** The number of orbits on `k`-tuples, times `|G|`, is the
`k`-th power sum of the trace distribution. -/
theorem orbitCount_mul_card_group (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] [Finite X] (k : ℕ) :
    orbitCount G X k * Nat.card G
      = (Multiset.map (fun a => a ^ k) (traceDistribution G X)).sum := by
  rw [powerSum_traceDistribution, orbitCount, ← burnside G (Fin k → X)]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact fixedCard_pi (G := G) X g k

/-! ## Elementary structure of the trace distribution -/

theorem fixedCard_le {G : Type*} [Group G] (X : Type*) [MulAction G X] [Finite X] (g : G) :
    fixedCard X g ≤ Nat.card X :=
  Nat.card_le_card_of_injective _ Subtype.val_injective

theorem fixedCard_one {G : Type*} [Group G] (X : Type*) [MulAction G X] :
    fixedCard X (1 : G) = Nat.card X := by
  rw [fixedCard, fixedBy_one_eq_univ X G]
  exact Nat.card_congr (Equiv.Set.univ X)

theorem exists_of_mem_traceDistribution {G : Type*} [Group G] [Fintype G] (X : Type*)
    [MulAction G X] {a : ℕ} (h : a ∈ traceDistribution G X) : ∃ g : G, fixedCard X g = a := by
  rw [traceDistribution] at h
  obtain ⟨g, _, hg⟩ := Multiset.mem_map.mp h
  exact ⟨g, hg⟩

theorem card_mem_traceDistribution (G : Type*) [Group G] [Fintype G] (X : Type*)
    [MulAction G X] : Nat.card X ∈ traceDistribution G X := by
  rw [traceDistribution]
  exact Multiset.mem_map.mpr ⟨1, Finset.mem_univ_val 1, fixedCard_one X⟩

theorem le_card_of_mem_traceDistribution {G : Type*} [Group G] [Fintype G] (X : Type*)
    [MulAction G X] [Finite X] {a : ℕ} (h : a ∈ traceDistribution G X) : a ≤ Nat.card X := by
  obtain ⟨g, rfl⟩ := exists_of_mem_traceDistribution X h
  exact fixedCard_le X g

/-- The trace distribution knows the size of the set it came from: `|X|` is its largest
entry, realised at the identity. -/
theorem card_eq_of_traceDistribution_eq {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
    (h : traceDistribution G X = traceDistribution G Y) : Nat.card X = Nat.card Y := by
  have h1 : Nat.card X ≤ Nat.card Y :=
    le_card_of_mem_traceDistribution Y (h ▸ card_mem_traceDistribution G X)
  have h2 : Nat.card Y ≤ Nat.card X :=
    le_card_of_mem_traceDistribution X (h.symm ▸ card_mem_traceDistribution G Y)
  omega

/-! ## The main equivalence -/

/-- The easy direction: equal trace distributions force equal orbit counts on
`k`-tuples for **every** `k`, by graded Burnside plus cancellation of `|G| > 0`. -/
theorem card_orbits_eq_of_traceDistribution_eq {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
    (h : traceDistribution G X = traceDistribution G Y) (k : ℕ) :
    orbitCount G X k = orbitCount G Y k := by
  have hG : 0 < Nat.card G := Nat.card_pos
  have hX := orbitCount_mul_card_group G X k
  have hY := orbitCount_mul_card_group G Y k
  have : orbitCount G X k * Nat.card G = orbitCount G Y k * Nat.card G := by
    rw [hX, hY, h]
  exact Nat.eq_of_mul_eq_mul_right hG this

/-- The hard direction: agreement of the orbit counts on `k`-tuples for the finitely
many `k ≤ max |X| |Y|` already forces the two trace distributions to coincide.

The proof feeds graded Burnside into the interpolation-duality rigidity theorem
`multiset_eq_of_powerSum_eq`. -/
theorem traceDistribution_eq_of_card_orbits_eq {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
    (h : ∀ k ≤ max (Nat.card X) (Nat.card Y), orbitCount G X k = orbitCount G Y k) :
    traceDistribution G X = traceDistribution G Y := by
  refine multiset_eq_of_powerSum_eq (n := max (Nat.card X) (Nat.card Y) + 1) ?_ ?_ ?_
  · intro a ha
    have := le_card_of_mem_traceDistribution X ha
    have : Nat.card X ≤ max (Nat.card X) (Nat.card Y) := le_max_left _ _
    omega
  · intro b hb
    have := le_card_of_mem_traceDistribution Y hb
    have : Nat.card Y ≤ max (Nat.card X) (Nat.card Y) := le_max_right _ _
    omega
  · intro k hk
    rw [← orbitCount_mul_card_group G X k, ← orbitCount_mul_card_group G Y k,
      h k (Nat.lt_succ_iff.mp hk)]

/-- **Main theorem (Conjecture A).**  Two finite `G`-actions have the same trace
distribution `{|X^g| : g ∈ G}` if and only if they have the same number of orbits on
`k`-tuples for every `k ≤ max |X| |Y|`. -/
theorem traceDistribution_eq_iff_card_orbits_eq {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y] :
    traceDistribution G X = traceDistribution G Y
      ↔ ∀ k ≤ max (Nat.card X) (Nat.card Y), orbitCount G X k = orbitCount G Y k :=
  ⟨fun h k _ => card_orbits_eq_of_traceDistribution_eq X Y h k,
   traceDistribution_eq_of_card_orbits_eq X Y⟩

/-- **Rigidity / bootstrapping.**  Agreement of the orbit counts on `k`-tuples for the
finitely many `k ≤ max |X| |Y|` propagates to *all* `k`. -/
theorem card_orbits_eq_of_le {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
    (h : ∀ k ≤ max (Nat.card X) (Nat.card Y), orbitCount G X k = orbitCount G Y k) :
    ∀ k, orbitCount G X k = orbitCount G Y k :=
  card_orbits_eq_of_traceDistribution_eq X Y (traceDistribution_eq_of_card_orbits_eq X Y h)

/-! ## A bound that does not depend on `|X|`

The joint support of the two trace distributions has at most `2·|G|` distinct values,
simply because each distribution has exactly `|G|` entries.  Feeding this into the
*support* form of power-sum rigidity gives a threshold that is independent of the size
of the sets acted on — a genuine improvement whenever a small group acts on a large
set (e.g. `ℤ/2` acting on a million points: `k < 4` already suffices). -/

theorem card_traceDistribution (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] : Multiset.card (traceDistribution G X) = Nat.card G := by
  rw [traceDistribution]
  simp [Nat.card_eq_fintype_card]

/-- **Group-order bound.**  Agreement of the orbit counts on `k`-tuples for the
`2·|G|` values `k < 2·|G|` already forces the trace distributions to agree — no matter
how large `X` and `Y` are. -/
theorem traceDistribution_eq_of_card_orbits_eq_group_bound {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
    (h : ∀ k < 2 * Nat.card G, orbitCount G X k = orbitCount G Y k) :
    traceDistribution G X = traceDistribution G Y := by
  classical
  refine multiset_eq_of_powerSum_eq_of_support (n := 2 * Nat.card G) ?_ ?_
  · calc (traceDistribution G X + traceDistribution G Y).toFinset.card
        ≤ Multiset.card (traceDistribution G X + traceDistribution G Y) :=
          Multiset.toFinset_card_le _
      _ = 2 * Nat.card G := by
          rw [Multiset.card_add, card_traceDistribution, card_traceDistribution]
          ring
  · intro k hk
    rw [← orbitCount_mul_card_group G X k, ← orbitCount_mul_card_group G Y k, h k hk]

/-- The group-order bound in `iff` form. -/
theorem traceDistribution_eq_iff_card_orbits_eq_group_bound {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y] :
    traceDistribution G X = traceDistribution G Y
      ↔ ∀ k < 2 * Nat.card G, orbitCount G X k = orbitCount G Y k :=
  ⟨fun h k _ => card_orbits_eq_of_traceDistribution_eq X Y h k,
   traceDistribution_eq_of_card_orbits_eq_group_bound X Y⟩

/-- **Combined threshold.**  Only the first
`min (2·|G|) (max |X| |Y| + 1)` orbit counts are ever needed. -/
theorem card_orbits_eq_of_lt_min {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
    (h : ∀ k < min (2 * Nat.card G) (max (Nat.card X) (Nat.card Y) + 1),
      orbitCount G X k = orbitCount G Y k) :
    ∀ k, orbitCount G X k = orbitCount G Y k := by
  refine card_orbits_eq_of_traceDistribution_eq X Y ?_
  rcases le_total (2 * Nat.card G) (max (Nat.card X) (Nat.card Y) + 1) with hle | hle
  · refine traceDistribution_eq_of_card_orbits_eq_group_bound X Y fun k hk => ?_
    exact h k (by omega)
  · refine traceDistribution_eq_of_card_orbits_eq X Y fun k hk => ?_
    exact h k (by omega)

/-! ## The gradewise q-series form -/

/-- The coefficients of the q-series are exactly the multiplicities of the trace
distribution. -/
theorem coeff_traceSeries (G : Type*) [Group G] [Fintype G] (X : Type*) [MulAction G X]
    (m : ℕ) : (traceSeries G X).coeff m = ((traceDistribution G X).count m : ℤ) := by
  classical
  rw [traceSeries, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole, traceDistribution, Multiset.count_map]
  norm_cast

/-- The q-series is a *complete* invariant of the trace distribution. -/
theorem traceSeries_eq_iff_traceDistribution_eq {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] :
    traceSeries G X = traceSeries G Y ↔ traceDistribution G X = traceDistribution G Y := by
  constructor
  · intro h
    ext m
    have := congrArg (fun p => Polynomial.coeff p m) h
    simp only [coeff_traceSeries] at this
    exact_mod_cast this
  · intro h
    ext m
    rw [coeff_traceSeries, coeff_traceSeries, h]

/-- **Gradewise q-series form of Conjecture A.**  The fixed-point generating
polynomials `∑_{g ∈ G} q^{|X^g|}` of two finite `G`-actions coincide iff the actions
have the same number of orbits on `k`-tuples for all `k ≤ max |X| |Y|` — and then, by
`card_orbits_eq_of_le`, for all `k`. -/
theorem traceDistribution_graded_eq {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y] :
    traceSeries G X = traceSeries G Y
      ↔ ∀ k ≤ max (Nat.card X) (Nat.card Y), orbitCount G X k = orbitCount G Y k :=
  (traceSeries_eq_iff_traceDistribution_eq X Y).trans
    (traceDistribution_eq_iff_card_orbits_eq X Y)

end TraceDistribution
section
open MulAction Finset
open TraceDistribution

theorem solution {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
    (h : ∀ k ≤ max (Nat.card X) (Nat.card Y), orbitCount G X k = orbitCount G Y k) :
    traceDistribution G X = traceDistribution G Y :=
  @TraceDistribution.traceDistribution_eq_of_card_orbits_eq G _ _ X Y _ _ _ _ h

end
