-- Prove2me | Theorems.Thm_KitchenQuery_queryList_eval
-- name    : KitchenQuery.queryList_eval
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:04:32.16389+00:00
-- url     : https://prove2.me/theorems/62e5cd02-be85-4024-951b-a6522880d878
-- title:
--   QueryList eval
-- statement:
--   Formal statement of `KitchenQuery.queryList_eval` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem KitchenQuery.queryList_eval(L : List (Fin n)) (cont : Pantry n → Taste n) (a x : Pantry n) :
--       (queryList L cont a).eval x
--         = (cont (fun j => if j ∈ L then x j else a j)).eval x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KitchenCertificateSquare.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KitchenCertificateSquare.lean#L59

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

theorem KitchenQuery.queryList_eval(L : List (Fin n)) (cont : Pantry n → Taste n) (a x : Pantry n) :
    (queryList L cont a).eval x
      = (cont (fun j => if j ∈ L then x j else a j)).eval x := by sorry
