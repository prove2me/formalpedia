-- Prove2me | solution 1 for Bridges.ResidueLeakage.qrFingerprint_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:44:12.763805+00:00
-- url     : https://prove2.me/submissions/57d4d753-f478-4a13-96d1-5b7cc654d1aa

-- Sol generated from Bridges/ResidueLeakageBoundary.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_congr
/-
# Adversarial review: where the no-pruning theorem stops, and why

Fourth file of the residue-leakage thread.  Stage-4 critique of
`dirichlet_no_pruning`: its hypotheses are not decoration.

* `qrFingerprint_mul_sq` — the fingerprint is a *square-class* invariant:
  `F(m·s²) = F(m)`.  So `F_A` can never determine `N`; it only sees the class of
  `N` in `(ℤ/4∏A)ˣ / squares`.  This is the structural reason the "collision-free
  hash" reading of the experiment is false.
* `probe_divisor_forces_factor` — the sharp boundary of no-pruning: if some probe
  prime `a` *divides* the target `N₀`, then the fingerprint prunes completely —
  the only consistent second factor is `q = a`.  Hence the coprimality
  hypothesis in `dirichlet_no_pruning` is necessary, and the only pruning power
  the residue channel ever has is the trivial detection of a tiny prime factor,
  which trial division finds anyway.
* `qrFingerprint_eq_of_dvd_probe` — in that degenerate case the fingerprint has a
  `0` entry, i.e. the leak is visible directly in the data.
-/


open Bridges.ResidueLeakage





open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime) {m s : ℕ}
    (hm : m ≠ 0) (hs : s ≠ 0) (hcop : ∀ a ∈ A, ¬ a ∣ s) :
    qrFingerprint A (m * s ^ 2) = qrFingerprint A m := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero s := ⟨hs⟩
  refine qrFingerprint_congr fun a ha => ?_
  have hcopa : Int.gcd (a : ℤ) (s : ℕ) = 1 := by
    have : Nat.Coprime a s := (Nat.Prime.coprime_iff_not_dvd (hA a ha)).2 (hcop a ha)
    simpa [Int.gcd_natCast_natCast] using this
  have hsq : jacobiSym (a : ℤ) s * jacobiSym (a : ℤ) s = 1 := by
    rcases jacobiSym.eq_one_or_neg_one hcopa with h | h <;> rw [h] <;> norm_num
  calc jacobiSym (a : ℤ) (m * s ^ 2)
      = jacobiSym (a : ℤ) (m * (s * s)) := by rw [sq]
    _ = jacobiSym (a : ℤ) m * (jacobiSym (a : ℤ) s * jacobiSym (a : ℤ) s) := by
        rw [jacobiSym.mul_right (a : ℤ) m (s * s), jacobiSym.mul_right (a : ℤ) s s]
    _ = jacobiSym (a : ℤ) m := by rw [hsq, mul_one]
