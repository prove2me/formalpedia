-- Prove2me | solution 1 for KitchenQuery.cert_inter_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:08:34.758989+00:00
-- url     : https://prove2.me/submissions/c07cbb2f-df98-4d7b-af6c-42340e84aed5

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
theorem solution{f : Dish n} {x y : Pantry n} {S T : Finset (Fin n)}
    (hS : IsCertificate f x S) (hT : IsCertificate f y T) (hne : f x ≠ f y) :
    (S ∩ T).Nonempty := by
  classical
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  set u : Pantry n := fun j => if j ∈ S then x j else y j with hu
  have h1 : f u = f x := hS u (fun j hj => by simp [hu, hj])
  have h2 : f u = f y := by
    refine hT u (fun j hj => ?_)
    have hjS : j ∉ S := by
      intro hc
      have : j ∈ S ∩ T := Finset.mem_inter.2 ⟨hc, hj⟩
      simp [hemp] at this
    simp [hu, hjS]
  exact hne (h1.symm.trans h2)
