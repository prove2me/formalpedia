-- Prove2me | solution 1 for Bridges.ResidueLeakage.probe_divisor_forces_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:44:12.208261+00:00
-- url     : https://prove2.me/submissions/543534bc-006e-419e-ac06-5197f7b5a40d

-- Sol generated from Bridges/ResidueLeakageBoundary.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
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


/-- If a probe prime divides `N₀`, the corresponding fingerprint entry is `0`:
the degenerate case is visible in the data. -/
theorem qrFingerprint_eq_of_dvd_probe {N₀ a : ℕ}
    (hdvd : a ∣ N₀) (hN₀ : N₀ ≠ 0) (ha1 : 1 < a) :
    jacobiSym (a : ℤ) N₀ = 0 := by
  rw [jacobiSym.eq_zero_iff]
  refine ⟨hN₀, ?_⟩
  have : Nat.gcd a N₀ = a := Nat.gcd_eq_left hdvd
  simp [Int.gcd_natCast_natCast, this]
  omega



open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    {N₀ p q a : ℕ} (ha : a ∈ A) (hdvd : a ∣ N₀) (hN₀ : N₀ ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hap : a ≠ p)
    (hcons : qrFingerprint A (p * q) = qrFingerprint A N₀) : q = a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hprime : a.Prime := hA a ha
  have hzero : jacobiSym (a : ℤ) N₀ = 0 :=
    qrFingerprint_eq_of_dvd_probe hdvd hN₀ hprime.one_lt
  have hentry : jacobiSym (a : ℤ) (p * q) = jacobiSym (a : ℤ) N₀ :=
    List.map_inj_left.1 hcons a ha
  have hmul : jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) q = 0 := by
    rw [← jacobiSym.mul_right (a : ℤ) p q, hentry, hzero]
  have hpne : jacobiSym (a : ℤ) p ≠ 0 := by
    have hcop : Int.gcd (a : ℤ) (p : ℕ) = 1 := by
      simpa [Int.gcd_natCast_natCast] using (Nat.coprime_primes hprime hp).2 hap
    rcases jacobiSym.eq_one_or_neg_one hcop with h | h <;> rw [h] <;> norm_num
  have hqzero : jacobiSym (a : ℤ) q = 0 := by
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd h hpne
    · exact h
  have hnc : ¬ Int.gcd (a : ℤ) (q : ℕ) = 1 := (jacobiSym.eq_zero_iff.1 hqzero).2
  by_contra hne
  exact hnc (by
    simpa [Int.gcd_natCast_natCast] using
      (Nat.coprime_primes hprime hq).2 (fun h => hne h.symm))
