-- Prove2me | solution 1 for KitchenQuery.queryList_eval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:18:22.471699+00:00
-- url     : https://prove2.me/submissions/ec67ddf7-5cfe-40c2-ba94-7fcd2d98e67a

-- Sol generated from Novelty/KitchenCertificateSquare.lean
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






open KitchenQuery in
theorem solution(L : List (Fin n)) (cont : Pantry n → Taste n) (a x : Pantry n) :
    (queryList L cont a).eval x
      = (cont (fun j => if j ∈ L then x j else a j)).eval x := by
  classical
  induction L generalizing a with
  | nil => simp [queryList]
  | cons i L ih =>
      have hkey : ∀ b : Bool, x i = b →
          (queryList L cont (Function.update a i b)).eval x
            = (cont (fun j => if j ∈ i :: L then x j else a j)).eval x := by
        intro b hb
        rw [ih]
        congr 2
        funext j
        by_cases hjL : j ∈ L
        · simp [hjL, List.mem_cons]
        · by_cases hji : j = i
          · subst hji; simp [hjL, hb]
          · simp [hjL, hji, List.mem_cons]
      cases hx : x i
      · simpa [queryList, Taste.eval, hx] using hkey false hx
      · simpa [queryList, Taste.eval, hx] using hkey true hx
