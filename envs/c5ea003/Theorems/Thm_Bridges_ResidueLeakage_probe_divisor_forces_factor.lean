-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_probe_divisor_forces_factor
-- name    : Bridges.ResidueLeakage.probe_divisor_forces_factor
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:34:43.667401+00:00
-- url     : https://prove2.me/theorems/44064159-630e-4533-9e2f-296a2f587f11
-- title:
--   Sharp boundary of no-pruning.
-- statement:
--   **Sharp boundary of no-pruning.**  If some probe prime `a` divides the
--   target `N₀`, then the residue data *does* prune: for any candidate prime `p ≠ a`
--   the only prime `q` with `F_A(p·q) = F_A(N₀)` is `q = a`.  So the coprimality
--   hypothesis of `dirichlet_no_pruning` cannot be dropped — and the only pruning
--   the channel ever achieves is the trivial discovery of a probe-size factor.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.probe_divisor_forces_factor{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
--       {N₀ p q a : ℕ} (ha : a ∈ A) (hdvd : a ∣ N₀) (hN₀ : N₀ ≠ 0)
--       (hp : p.Prime) (hq : q.Prime) (hap : a ≠ p)
--       (hcons : qrFingerprint A (p * q) = qrFingerprint A N₀) : q = a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakageBoundary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakageBoundary.lean#L56

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

theorem Bridges.ResidueLeakage.probe_divisor_forces_factor{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    {N₀ p q a : ℕ} (ha : a ∈ A) (hdvd : a ∣ N₀) (hN₀ : N₀ ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hap : a ≠ p)
    (hcons : qrFingerprint A (p * q) = qrFingerprint A N₀) : q = a := by sorry
