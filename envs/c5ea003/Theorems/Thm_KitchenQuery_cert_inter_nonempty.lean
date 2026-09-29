-- Prove2me | Theorems.Thm_KitchenQuery_cert_inter_nonempty
-- name    : KitchenQuery.cert_inter_nonempty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:04:24.302342+00:00
-- url     : https://prove2.me/theorems/9dc68a25-d967-43f4-9687-1c359841c1cf
-- title:
--   Goodness proofs and badness proofs always overlap.
-- statement:
--   **Goodness proofs and badness proofs always overlap.**  If `S` certifies the verdict at
--   `x` and `T` certifies the opposite verdict at `y`, then `S` and `T` share an ingredient.
--
--   ```lean
--   theorem KitchenQuery.cert_inter_nonempty{f : Dish n} {x y : Pantry n} {S T : Finset (Fin n)}
--       (hS : IsCertificate f x S) (hT : IsCertificate f y T) (hne : f x ≠ f y) :
--       (S ∩ T).Nonempty := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KitchenCertificateSquare.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KitchenCertificateSquare.lean#L84

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

theorem KitchenQuery.cert_inter_nonempty{f : Dish n} {x y : Pantry n} {S T : Finset (Fin n)}
    (hS : IsCertificate f x S) (hT : IsCertificate f y T) (hne : f x ≠ f y) :
    (S ∩ T).Nonempty := by sorry
