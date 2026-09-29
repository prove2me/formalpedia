-- Prove2me | Theorems.Thm_KitchenQuery_tasteCost_le_cert_mul
-- name    : KitchenQuery.tasteCost_le_cert_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:05:33.880921+00:00
-- url     : https://prove2.me/theorems/32337dc7-4350-4ffc-b1d9-129e1ccf193e
-- title:
--   `D(f) ≤ C₀(f) · C₁(f)` in the kitchen.
-- statement:
--   **`D(f) ≤ C₀(f) · C₁(f)` in the kitchen.**  Short goodness proofs together with short
--   badness proofs give an outright fast adaptive tasting protocol.
--
--   ```lean
--   theorem KitchenQuery.tasteCost_le_cert_mul(m : ℕ) : ∀ (k : ℕ) (f : Dish n),
--       (∀ x, f x = false → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ k) →
--       (∀ x, f x = true → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ m) →
--       tasteCost f ≤ k * m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KitchenCertificateSquare.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KitchenCertificateSquare.lean#L126

-- Thm stub generated from Novelty/KitchenCertificateSquare.lean
import Mathlib
import Definitions.Def_Novelty_KitchenCertificateSquare
import Definitions.Def_Novelty_KitchenQueryComplexity

/-!
# `P = NP ∩ co-NP`, up to squaring, in the kitchen

Third research cycle on the query model of `Novelty.KitchenQueryComplexity`.

Cycle 1 separated deterministic from nondeterministic verification (`kitchen_P_ne_NP`) and
showed the soufflé has no nondeterministic shortcut at either verdict.  That raises the sharp
question: *if a dish has short goodness proofs and short badness proofs, must it be quick to
taste outright?*  The answer proved here is yes, up to a product:

> **Main theorem** (`tasteCost_le_cert_mul`).  If every good pantry has a goodness
> certificate of at most `m` probes and every bad pantry has a badness certificate of at most
> `k` probes, then there is a deterministic adaptive taster using at most `k * m` probes.

Equivalently `D(f) ≤ C₀(f) · C₁(f)`: in the kitchen, `NP ∩ co-NP` collapses into `P` at the
cost of squaring the tasting time.  This is exactly the boundary that the soufflé escapes:
`souffle_no_certificate_shortcut` shows both of its certificate complexities are `n`, so the
theorem only yields the vacuous bound `n²`, whereas for `anySpoiled` the bound `1 · n = n` is
attained exactly (`anySpoiled_bound_tight`).

The proof is the classical adaptive covering argument, formalised in three pieces:

* `cert_inter_nonempty`: a goodness certificate and a badness certificate always overlap —
  the combinatorial heart.
* `restrictDish`, `restrict_isCertificate`: fixing the ingredients of a certificate shrinks
  every opposite certificate by at least one probe.
* `queryList`: the tasting strategy that probes a whole checklist and then continues
  adaptively, with its depth and evaluation laws.
-/

open KitchenQuery

open Finset

variable {n : ℕ}

/-! ### Probing a whole checklist, then continuing -/




/-! ### Certificates overlap -/


/-! ### Restricting a dish along a checklist -/



/-! ### The main theorem -/

theorem KitchenQuery.tasteCost_le_cert_mul(m : ℕ) : ∀ (k : ℕ) (f : Dish n),
    (∀ x, f x = false → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ k) →
    (∀ x, f x = true → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ m) →
    tasteCost f ≤ k * m := by sorry
