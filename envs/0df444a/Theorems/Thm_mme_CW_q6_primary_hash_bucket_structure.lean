-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_bucket_structure
-- name    : mme_CW_q6_primary_hash_bucket_structure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:50:52.160713+00:00
-- url     : https://prove2.me/theorems/057c3e6a-a21e-4950-a956-2a18958a9ea6
-- title:
--   Exact q=6 affine bucket has bounded Z-fibers and supported-mix closure
-- statement:
--   Fix a regular exact coupled q=6 profile and one literal retained affine-hash bucket $E$. Its represented Z-word set has cardinality at most\n\n$$\n\binom{2N}{L}\binom{2N-L}{L},\n$$\n\nand every represented Z-fiber contains at most $\binom{2G}{G}$ addresses. Moreover, if the X-mode of one bucket address, the Y-mode of another, and the Z-mode of a third form a coordinatewise-supported mixed address, then those three modes occur together on an address still lying in $E$.\n\nThe cardinality bounds are inherited from exact profile regularity. Closure follows because the doubled hash progression identity and the lower-half three-term-progression-free condition force the three retained labels to agree. This theorem is deterministic for fixed hash parameters and contains no averaging, collision deletion, or tensor realization.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), exact q=6 profile degrees and retained affine-hash closure on journal pp. 270--271, using the progression identity from pp. 259--260; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_q6_primary_hash_bucket
import Theorems.Thm_mme_CW_q6_hash_bucket_coherence

open MME

theorem mme_CW_q6_primary_hash_bucket_structure
    (N L G Xcount : ℕ)
    (hregular : CWQ6ExactAddressRegularity N L G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range ((4 * Xcount ^ 2 + 1) / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (b0 : ZMod (4 * Xcount ^ 2 + 1))
    (w : Fin (2 * N) → ZMod (4 * Xcount ^ 2 + 1)) :
    let E := cwQ6PrimaryHashBucket N L G Xcount S b0 w
    (E.image (fun e => e.1 2)).card ≤
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L ∧
    (∀ c ∈ E.image (fun e => e.1 2),
      (E.filter (fun e => e.1 2 = c)).card ≤ Nat.choose (2 * G) G) ∧
    ∀ ex ∈ E, ∀ ey ∈ E, ∀ ez ∈ E,
      CWQ6CoupledCoordinatewiseSupported
          (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
        ∃ e' ∈ E,
          e'.1 0 = ex.1 0 ∧
          e'.1 1 = ey.1 1 ∧
          e'.1 2 = ez.1 2 := by sorry
