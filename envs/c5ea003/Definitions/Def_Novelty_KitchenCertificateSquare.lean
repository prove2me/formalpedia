-- Prove2me | Definitions.Def_Novelty_KitchenCertificateSquare
-- name    : Novelty_KitchenCertificateSquare
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:30:29.117774+00:00
-- url     : https://prove2.me/theorems/d5b42336-0158-4657-9a02-b6cf2858e82b
-- title:
--   Aether Catalog definitions — Novelty_KitchenCertificateSquare
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KitchenCertificateSquare`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KitchenCertificateSquare.lean by skeleton subtraction
import Mathlib
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

namespace KitchenQuery

open Finset

variable {n : ℕ}

/-! ### Probing a whole checklist, then continuing -/

/-- Probe the ingredients of the list `L` one after another, remembering the answers in the
accumulator `a`, and then continue with `cont` applied to the accumulated knowledge. -/
def queryList : List (Fin n) → (Pantry n → Taste n) → Pantry n → Taste n
  | [], cont, a => cont a
  | (i :: L), cont, a =>
      .probe i (queryList L cont (Function.update a i false))
        (queryList L cont (Function.update a i true))



/-! ### Certificates overlap -/


/-! ### Restricting a dish along a checklist -/

/-- The dish obtained by fixing the ingredients of `S` to the observed values `a`. -/
def restrictDish (f : Dish n) (S : Finset (Fin n)) (a : Pantry n) : Dish n :=
  fun y => f (fun j => if j ∈ S then a j else y j)


/-! ### The main theorem -/





end KitchenQuery


