-- Prove2me | Definitions.Def_Bridges_PolyaTreeRecurrence
-- name    : Bridges_PolyaTreeRecurrence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:10.963365+00:00
-- url     : https://prove2.me/theorems/f981d090-26fe-4be4-94e9-abf2207df2b5
-- title:
--   Aether Catalog definitions — Bridges_PolyaTreeRecurrence
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PolyaTreeRecurrence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PolyaTreeRecurrence.lean by skeleton subtraction
import Mathlib

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

namespace PolyaTree

open Finset

/-- The arithmetic divisor weight `ωₙ = Σ_{d ∣ n} d · a_d`. -/
noncomputable def omegaSeq (a : ℕ → ℚ) (n : ℕ) : ℚ := ∑ d ∈ n.divisors, (d : ℚ) * a d

/-- The `n`-th coefficient of `S(z) = Σ_{i≥1} A(zⁱ)/i`, namely `[zⁿ]S = Σ_{i ∣ n} a_{n/i}/i`. -/
noncomputable def sCoeff (a : ℕ → ℚ) (n : ℕ) : ℚ := ∑ i ∈ n.divisors, a (n / i) / (i : ℚ)





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

end PolyaTree


