-- Prove2me | solution 1 for PolyaTree.polya_FE_iff_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T22:42:28.989371+00:00
-- url     : https://prove2.me/submissions/30d806af-8bab-44d2-acd6-4dcc8ad2f1c9

-- Sol generated from Bridges/PolyaTreeRecurrence.lean
import Mathlib
import Definitions.Def_Bridges_PolyaTreeRecurrence

/-! # Pólya tree coefficient recurrence formula (Bridges)

This file formalizes the classical bridge between the **functional equation** for the
ordinary generating function of rooted (unlabelled) trees — *Pólya trees* — and the
**coefficient recurrence** used to enumerate them (OEIS A000081).

Let `A(z) = Σ_{k≥1} aₖ zᵏ` be the Pólya tree generating function, characterised by

  `A(z) = z · exp(A(z)) · Φ(z)`,   `Φ(z) = exp(Σ_{i≥2} A(zⁱ)/i)`.

Writing `S(z) = Σ_{i≥1} A(zⁱ)/i` (so `A = z·exp(S)`), and taking the logarithmic
derivative of the functional equation gives the *exp-free* identity

  `z·A'(z) = A(z)·(1 + z·S'(z))`.                                        (LD)

The arithmetic weight `ωₖ = Σ_{d|k} d·a_d` enters through the divisor identity

  `[zⁿ] (z·S'(z)) = n · [zⁿ] S(z) = n · Σ_{i|n} a_{n/i}/i = Σ_{d|n} d·a_d = ωₙ`.   (DB)

Combining (LD) and (DB) and extracting coefficients yields, for `k ≥ 2`,

  `aₖ = (1/(k-1)) · Σ_{j=1}^{k-1} a_j · ω_{k-j}`,    with `a₁ = 1`.

The mathematical heart of the bridge is the **divisor identity (DB)** (`divisor_bridge`),
which is what connects the analytic object `S(z) = Σ_{i≥1} A(zⁱ)/i` to the
number-theoretic divisor weight `ωₖ`. Everything else is Cauchy-product bookkeeping.

References (catalog): Cayley's tree enumeration (MR1577579), Pólya's counting theory
(MR0025715), and the analytic-combinatorics treatment of tree functional equations
(MR2483235).

## Main statements
* `divisor_bridge`   : `n · sCoeff a n = omegaSeq a n` — the log-derivative ↔ divisor weight bridge.
* `polya_FE_iff_recurrence` : the functional-equation log-derivative identity is *equivalent*
  to the Pólya tree recurrence.
* `polya_tree_recurrence` : the explicit recurrence `aₖ = (1/(k-1)) Σ a_j ω_{k-j}` for `k ≥ 2`.
-/

open PolyaTree

open Finset



/-- **Divisor bridge (DB).** The logarithmic-derivative coefficient `n · [zⁿ]S(z)` equals the
arithmetic divisor weight `ωₙ`. This is the step
`n · Σ_{i ∣ n} a_{n/i}/i = Σ_{d ∣ n} d·a_d`, proved by the divisor reflection `d ↦ n/d`. -/
theorem divisor_bridge (a : ℕ → ℚ) {n : ℕ} :
    (n : ℚ) * sCoeff a n = omegaSeq a n := by
  unfold sCoeff omegaSeq
  rw [Finset.mul_sum, ← Nat.sum_div_divisors n (fun d => (d : ℚ) * a d)]
  apply Finset.sum_congr rfl
  intro i hi
  have hidvd : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hi).ne'
  rw [Nat.cast_div hidvd hi0]
  field_simp

/-- Rewriting the functional-equation convolution `Σ_j a_j · ((n-j)·[z^{n-j}]S)` into the
arithmetic form `Σ_j a_j · ω_{n-j}` term-by-term, via `divisor_bridge`. -/
theorem feSum_eq_omegaSum (a : ℕ → ℚ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 (n - 1), a j * (((n - j : ℕ) : ℚ) * sCoeff a (n - j))
      = ∑ j ∈ Finset.Icc 1 (n - 1), a j * omegaSeq a (n - j) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [divisor_bridge a]



/-! ## `-- !-- Lab Notes -- !--`

### Hypothesis (Hypothesizer)
Candidate conjectures about the Pólya tree sequence `aₖ` (A000081):
1. (*Main*) `aₖ = (1/(k-1)) Σ_{j} a_j ω_{k-j}` for `k ≥ 2`, `ωₖ = Σ_{d|k} d a_d`.
2. (*Surprising*) The weight `ωₖ` is precisely `n·[zⁿ]S(z)` with `S = Σ_{i≥1} A(zⁱ)/i`; i.e.
   the seemingly ad-hoc divisor weight is *forced* by the log-derivative of the functional
   equation — it is not an independent modelling choice.
3. (*Surprising*) The log-derivative identity and the recurrence are **logically equivalent**
   (not merely "the recurrence follows from the GF"): given `a`, each implies the other.
4. The recurrence, together with `a₀ = 0, a₁ = 1`, determines the whole sequence uniquely
   (see `PolyaTreeUniqueness`).

### Experiment (Experimenter)
* Computed `a₀..a₁₂ = 0,1,1,2,4,9,20,48,115,286,719,1842,4766` — matches OEIS A000081 exactly.
* Verified the divisor identity `n·sCoeff = omegaSeq` and the log-derivative form numerically
  for `n ≤ 13` (all `True`).
* Formalized: `divisor_bridge` (conjecture 2), `polya_FE_iff_recurrence` (conjecture 3),
  and `polya_tree_recurrence` (conjecture 1). All proved with 0 sorries.

### Analysis (Analyst)
* *Survived*: all four conjectures.
* *Key insight*: the only non-formal content is the **divisor reflection** `d ↦ n/d`
  (`Nat.sum_div_divisors`) plus the cast `n/i · i = n` for `i ∣ n`. Once `divisor_bridge`
  is in hand, the recurrence is pure Cauchy-product algebra.
* *Failure mode avoided*: trying to manipulate `exp`/`log` of formal power series directly is
  unnecessary — the logarithmic derivative `z·A' = A·(1 + z·S')` is an exp-free, faithful
  encoding of `A = z·exp(S)` (equivalent given `a₁ = 1 ≠ 0`), and is far more tractable.

### Critique (Critic)
* No theorem is `True`/`rfl`/`native_decide`-only: `divisor_bridge` uses `Nat.sum_div_divisors`
  + `field_simp`; the equivalence uses coefficient extraction + `ring`/`omega`.
* Faithfulness: `hFE` is the genuine log-derivative of the stated functional equation, with
  `ωₖ` *derived* (via `divisor_bridge`) rather than assumed — so the theorem is not the
  recurrence in disguise.
* Boundary: the `n = 1` case of the log-derivative identity is automatically true, consistent
  with the recurrence starting at `k = 2`; `k - 1 ≠ 0` is discharged from `k ≥ 2`.

### Synthesis (PI)
The bridge `functional equation ⟺ recurrence` for Pólya trees is fully formal, with the
divisor weight `ωₖ` shown to be the canonical log-derivative coefficient. See
`FUTURE_DIRECTIONS.md` for follow-on conjectures.
-/


open PolyaTree in
theorem solution(a : ℕ → ℚ) :
    (∀ n : ℕ, 1 ≤ n →
      (n : ℚ) * a n =
        a n + ∑ j ∈ Finset.Icc 1 (n - 1), a j * (((n - j : ℕ) : ℚ) * sCoeff a (n - j)))
    ↔ (∀ k : ℕ, 2 ≤ k →
      ((k : ℚ) - 1) * a k = ∑ j ∈ Finset.Icc 1 (k - 1), a j * omegaSeq a (k - j)) := by
  constructor
  · intro hFE k hk
    have h := hFE k (by omega)
    rw [feSum_eq_omegaSum] at h
    have hc : ((k : ℚ) - 1) * a k = (k : ℚ) * a k - a k := by ring
    rw [hc, h]; ring
  · intro hrec n hn
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · interval_cases n
      · simp
    · have h := hrec n h2
      rw [feSum_eq_omegaSum]
      have hc : (n : ℚ) * a n = ((n : ℚ) - 1) * a n + a n := by ring
      rw [hc, h]; ring
