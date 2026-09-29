-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_signVectors_ncard
-- name    : Bridges.ResidueLeakage.signVectors_ncard
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:33:43.986608+00:00
-- url     : https://prove2.me/theorems/7c67c70f-0eb1-40f2-ad76-533638e29ffb
-- title:
--   Exactly `2^n` sign vectors.
-- statement:
--   **Exactly `2^n` sign vectors.**
--
--   ```lean
--   theorem Bridges.ResidueLeakage.signVectors_ncard(n : ℕ) : (signVectors n).ncard = 2 ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakageCounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakageCounting.lean#L61

-- Thm stub generated from Bridges/ResidueLeakageCounting.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageCounting
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
/-
# Counting the leakage: the fingerprint carries exactly `K` bits

Sixth file of the residue-leakage thread.  `qrFingerprint_range_eq` identifies
the range of the fingerprint on primes with the set of `±1`-vectors of length
`K`.  Here we count that set, so that the leakage curve becomes an exact
number:

`|{ F_A(q) : q prime, q ∉ A }| = 2^K`.

Combined with `dirichlet_no_pruning` this is the quantitative form of the
verdict: the channel emits exactly `K` bits about `N`, and none of them about
the individual factors.
-/


open Bridges.ResidueLeakage

theorem Bridges.ResidueLeakage.signVectors_ncard(n : ℕ) : (signVectors n).ncard = 2 ^ n := by sorry
