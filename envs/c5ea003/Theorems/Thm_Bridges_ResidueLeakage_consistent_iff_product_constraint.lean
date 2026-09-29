-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_consistent_iff_product_constraint
-- name    : Bridges.ResidueLeakage.consistent_iff_product_constraint
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:31:25.993117+00:00
-- url     : https://prove2.me/theorems/66667254-1a78-4776-8263-4af2cdb666de
-- title:
--   Exact characterisation of consistency.
-- statement:
--   **Exact characterisation of consistency.**  For primes `p, q` outside the
--   probe set, the semiprime `p·q` has the observed fingerprint of `N₀` exactly when
--   the symmetric product relation holds at every probe prime.  Nothing else about
--   `p` and `q` is constrained by the residue channel.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.consistent_iff_product_constraint{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
--       {N₀ p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hpA : ∀ a ∈ A, a ≠ p) :
--       qrFingerprint A (p * q) = qrFingerprint A N₀ ↔
--         ∀ a ∈ A, jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) N₀ * jacobiSym (a : ℤ) p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueChannelCosetStructure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueChannelCosetStructure.lean#L28

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

theorem Bridges.ResidueLeakage.consistent_iff_product_constraint{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    {N₀ p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpA : ∀ a ∈ A, a ≠ p) :
    qrFingerprint A (p * q) = qrFingerprint A N₀ ↔
      ∀ a ∈ A, jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) N₀ * jacobiSym (a : ℤ) p := by sorry
