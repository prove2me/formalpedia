-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.KPow_succ_support
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T14:03:36.289907+00:00
-- url     : https://prove2.me/submissions/f1673813-6fba-4d3d-96a4-8a1721ee342c

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelPow
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin (File B): kernel composition and powers

Composition `KComp P Q n k = ∑_{j<n} P n j · Q j k` and the `L`-fold power `KPow L P` of a predecessor
kernel.  Proves nonnegativity and (strict) predecessor-support preservation by induction on `L` — the
algebraic foundation for the finite-time Doeblin overlap and the `P^L`-harmonic identity for `hitVal`.
The identity kernel `KPow 0 = δ(k=n)` forces the *strict* support `n < k → · = 0`.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Composition kills `n ≤ k` whenever the right kernel has strict predecessor support. -/
lemma KComp_support {P Q : ℕ → ℕ → ℝ} (hQ : ∀ a b, a < b → Q a b = 0)
    {n k : ℕ} (hnk : n ≤ k) : KComp P Q n k = 0 := by
  rw [KComp]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [hQ j k (by omega), mul_zero]

/-- `KPow L P` has strict predecessor support `n < k → · = 0`. -/
lemma KPow_support {P : ℕ → ℕ → ℝ} : ∀ (L : ℕ) {n k : ℕ}, n < k → KPow L P n k = 0 := by
  intro L
  induction L with
  | zero => intro n k hnk; simp only [KPow]; rw [if_neg (by omega)]
  | succ L ih => intro n k hnk; rw [KPow]; exact KComp_support (fun a b hab => ih hab) (le_of_lt hnk)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos in
theorem solution {P : ℕ → ℕ → ℝ} (L : ℕ) {n k : ℕ} (hnk : n ≤ k) :
    KPow (L + 1) P n k = 0 := by
  rw [KPow]
  exact KComp_support (fun a b hab => KPow_support L hab) hnk
