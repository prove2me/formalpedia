-- Prove2me | solution 1 for PolyaTree.polya_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:27:31.267954+00:00
-- url     : https://prove2.me/submissions/9f8e2cf0-19ae-4724-b8b0-370888de72c3

-- Sol generated from Bridges/PolyaTreeUniqueness.lean
import Mathlib
import Definitions.Def_Bridges_PolyaTreeRecurrence
/-! # Uniqueness of the Pólya tree sequence (Bridges)

The Pólya tree recurrence determines the entire sequence from its base values: any two
sequences `a, b : ℕ → ℚ` with `a₀ = b₀ = 0`, `a₁ = b₁ = 1` that both satisfy

  `aₖ = (1/(k-1)) Σ_{j=1}^{k-1} a_j · ω_{k-j}`   (and likewise for `b`)

are equal at every index. This complements `PolyaTreeRecurrence`: the functional equation
fixes a unique coefficient sequence (OEIS A000081).
-/

open PolyaTree

open Finset

/-- `omegaSeq` only depends on the values of the sequence at indices `≤ m`. -/
theorem omegaSeq_congr {a b : ℕ → ℚ} {m : ℕ} (h : ∀ d, d ≤ m → a d = b d) :
    omegaSeq a m = omegaSeq b m := by
  unfold omegaSeq
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.mem_divisors] at hd
  rw [h d (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1)]


/-! ## `-- !-- Lab Notes -- !--`

### Hypothesis
The recurrence + base data `a₀ = 0, a₁ = 1` determines a *unique* sequence (well-posedness).

### Experiment
Formalized `polya_unique` by strong induction; the supporting lemma `omegaSeq_congr` isolates
the locality of the divisor weight (`ωₘ` only sees indices `≤ m`).

### Analysis
The recurrence is *triangular*: term `k` is an explicit rational combination of strictly
earlier terms, so uniqueness is a clean strong-induction argument once locality of `ωₘ` is
established. The division by `k - 1` is well-defined because `k ≥ 2`.

### Critique
Not vacuous: the hypotheses are simultaneously satisfiable (A000081 over ℚ is a witness), and
the proof genuinely uses `Nat.strong_induction_on` + `omegaSeq_congr`, not `decide`.

### Synthesis
Together with `polya_tree_recurrence`, this shows the functional equation pins down a single
coefficient sequence — the bridge is an equivalence with a unique solution.
-/


open PolyaTree in
theorem solution(a b : ℕ → ℚ)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha1 : a 1 = 1) (hb1 : b 1 = 1)
    (hAr : ∀ k : ℕ, 2 ≤ k →
      a k = (1 / ((k : ℚ) - 1)) * ∑ j ∈ Finset.Icc 1 (k - 1), a j * omegaSeq a (k - j))
    (hBr : ∀ k : ℕ, 2 ≤ k →
      b k = (1 / ((k : ℚ) - 1)) * ∑ j ∈ Finset.Icc 1 (k - 1), b j * omegaSeq b (k - j)) :
    ∀ n, a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [ha0, hb0]
    | 1, _ => rw [ha1, hb1]
    | (k + 2), ih =>
      have hk : 2 ≤ k + 2 := by omega
      rw [hAr (k + 2) hk, hBr (k + 2) hk]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [ih j (by omega), omegaSeq_congr (fun d _ => ih d (by omega))]
