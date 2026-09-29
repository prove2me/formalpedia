-- Prove2me | solution 1 for Bridges.ResidueLeakage.consistent_iff_product_constraint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:22:04.419627+00:00
-- url     : https://prove2.me/submissions/73d45444-a64a-43d3-b9d3-9cf3b9e39dc3

-- Sol generated from Bridges/ResidueChannelCosetStructure.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
/-
# The residue channel is exactly one symmetric constraint: coset structure

Third file of the residue-leakage thread (after
`Bridges.ResidueLeakageDirichletNoPruning` and
`Bridges.ResidueLeakagePatternSurjectivity`).

The two previous files say that the QR fingerprint cannot prune the candidate
set and that every sign pattern occurs.  Here we pin down the *exact* shape of
the information the channel carries about a factorisation `N₀ = p·q`:

* `consistent_iff_product_constraint` — a pair of primes `(p,q)` is consistent
  with the observed fingerprint **iff** the single symmetric relation
  `(a|q) = (a|N₀)·(a|p)` holds for every probe prime `a`.  There is no further
  constraint: the consistent set is a coset of the "anti-diagonal" in
  `{±1}^K × {±1}^K`.
* `residue_channel_full_coset` — and that coset surjects onto the first factor:
  for *every* pattern `ε ∈ {±1}^K` there are primes `p, q` with `F(p) = ε` and
  `F(p·q) = F(N₀)`.  The `K` bits carried by `F(p)` are entirely free, i.e. the
  channel leaks `0` bits about the individual factor.
-/


open Bridges.ResidueLeakage




open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    {N₀ p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpA : ∀ a ∈ A, a ≠ p) :
    qrFingerprint A (p * q) = qrFingerprint A N₀ ↔
      ∀ a ∈ A, jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) N₀ * jacobiSym (a : ℤ) p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  rw [show qrFingerprint A (p * q) = A.map (fun a : ℕ => jacobiSym (a : ℤ) (p * q)) from rfl,
    show qrFingerprint A N₀ = A.map (fun a : ℕ => jacobiSym (a : ℤ) N₀) from rfl,
    List.map_inj_left]
  constructor
  · intro h a ha
    have hsq : jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) p = 1 := by
      have hcop : Int.gcd (a : ℤ) (p : ℕ) = 1 := by
        simpa [Int.gcd_natCast_natCast] using
          (Nat.coprime_primes (hA a ha) hp).2 (hpA a ha)
      rcases jacobiSym.eq_one_or_neg_one hcop with h' | h' <;> rw [h'] <;> norm_num
    have hmul := (jacobiSym.mul_right (a : ℤ) p q).symm.trans (h a ha)
    calc jacobiSym (a : ℤ) q
        = (jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) p) * jacobiSym (a : ℤ) q := by
          rw [hsq, one_mul]
      _ = jacobiSym (a : ℤ) p * (jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) q) := by ring
      _ = jacobiSym (a : ℤ) N₀ * jacobiSym (a : ℤ) p := by rw [hmul]; ring
  · intro h a ha
    have hsq : jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) p = 1 := by
      have hcop : Int.gcd (a : ℤ) (p : ℕ) = 1 := by
        simpa [Int.gcd_natCast_natCast] using
          (Nat.coprime_primes (hA a ha) hp).2 (hpA a ha)
      rcases jacobiSym.eq_one_or_neg_one hcop with h' | h' <;> rw [h'] <;> norm_num
    rw [jacobiSym.mul_right (a : ℤ) p q, h a ha]
    calc jacobiSym (a : ℤ) p * (jacobiSym (a : ℤ) N₀ * jacobiSym (a : ℤ) p)
        = jacobiSym (a : ℤ) N₀ * (jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) p) := by ring
      _ = jacobiSym (a : ℤ) N₀ := by rw [hsq, mul_one]
