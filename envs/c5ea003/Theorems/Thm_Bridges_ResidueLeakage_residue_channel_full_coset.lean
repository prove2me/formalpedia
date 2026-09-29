-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_residue_channel_full_coset
-- name    : Bridges.ResidueLeakage.residue_channel_full_coset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:33:11.981155+00:00
-- url     : https://prove2.me/theorems/f04985d2-0102-4688-8901-526a7840af47
-- title:
--   The consistent set surjects onto every pattern for the first factor.
-- statement:
--   **The consistent set surjects onto every pattern for the first factor.**
--   Given the observed fingerprint of `N₀` and *any* desired sign pattern `ε`, there
--   are primes `p, q` with `F(p) = ε` and `F(p·q) = F(N₀)`.  Hence observing
--   `F_A(N₀)` leaves all `K` bits of `F_A(p)` free: the residue channel transmits
--   nothing about the individual factor beyond the symmetric relation.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.residue_channel_full_coset{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
--       (hnd : A.Nodup) {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a)
--       {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
--       ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ qrFingerprint A p = A.map ε ∧
--         qrFingerprint A (p * q) = qrFingerprint A N₀ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueChannelCosetStructure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueChannelCosetStructure.lean#L66

-- Thm stub generated from Bridges/ResidueChannelCosetStructure.lean
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

theorem Bridges.ResidueLeakage.residue_channel_full_coset{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    (hnd : A.Nodup) {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a)
    {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ qrFingerprint A p = A.map ε ∧
      qrFingerprint A (p * q) = qrFingerprint A N₀ := by sorry
