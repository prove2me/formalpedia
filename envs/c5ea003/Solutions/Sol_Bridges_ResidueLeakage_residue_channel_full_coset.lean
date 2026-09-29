-- Prove2me | solution 1 for Bridges.ResidueLeakage.residue_channel_full_coset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:38:43.098277+00:00
-- url     : https://prove2.me/submissions/9393e24e-d803-4a53-8153-35d4ce615d39

-- Sol generated from Bridges/ResidueChannelCosetStructure.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Theorems.Thm_Bridges_ResidueLeakage_exists_compensating_prime
import Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_pattern_surjective
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
    (hnd : A.Nodup) {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a)
    {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ qrFingerprint A p = A.map ε ∧
      qrFingerprint A (p * q) = qrFingerprint A N₀ := by
  obtain ⟨p, hp, hpodd, hpf⟩ := (qrFingerprint_pattern_surjective hA hnd hε).nonempty
  have hpsym : ∀ a ∈ A, jacobiSym (a : ℤ) p = ε a := fun a ha =>
    List.map_inj_left.1 hpf a ha
  have hpA : ∀ a ∈ A, a ≠ p := by
    intro a ha hap
    have h0 : jacobiSym (a : ℤ) p = 0 := by
      subst hap
      haveI : NeZero a := ⟨(hA a ha).ne_zero⟩
      rw [jacobiSym.eq_zero_iff_not_coprime]
      simp [(hA a ha).one_lt.ne']
    rcases hε a ha with h | h <;> rw [hpsym a ha, h] at h0 <;> norm_num at h0
  obtain ⟨q, hq, hqf⟩ := exists_compensating_prime hA hN₀ hp hpodd hNA hpA
  exact ⟨p, q, hp, hq, hpf, hqf⟩
