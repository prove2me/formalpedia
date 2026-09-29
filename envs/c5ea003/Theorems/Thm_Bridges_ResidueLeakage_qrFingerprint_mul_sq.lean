-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_mul_sq
-- name    : Bridges.ResidueLeakage.qrFingerprint_mul_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:34:52.908981+00:00
-- url     : https://prove2.me/theorems/a8e0cb04-ac01-4958-8640-b645ec18a5b9
-- title:
--   Square-class invariance.
-- statement:
--   **Square-class invariance.**  Multiplying by a square coprime to the probe
--   primes does not change the fingerprint.  Consequently the fingerprint is an
--   invariant of the square class of `N` modulo `4∏A` and cannot identify `N`.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.qrFingerprint_mul_sq{A : List ℕ} (hA : ∀ a ∈ A, a.Prime) {m s : ℕ}
--       (hm : m ≠ 0) (hs : s ≠ 0) (hcop : ∀ a ∈ A, ¬ a ∣ s) :
--       qrFingerprint A (m * s ^ 2) = qrFingerprint A m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakageBoundary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakageBoundary.lean#L25

-- Thm stub generated from Bridges/ResidueLeakageBoundary.lean
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

theorem Bridges.ResidueLeakage.qrFingerprint_mul_sq{A : List ℕ} (hA : ∀ a ∈ A, a.Prime) {m s : ℕ}
    (hm : m ≠ 0) (hs : s ≠ 0) (hcop : ∀ a ∈ A, ¬ a ∣ s) :
    qrFingerprint A (m * s ^ 2) = qrFingerprint A m := by sorry
