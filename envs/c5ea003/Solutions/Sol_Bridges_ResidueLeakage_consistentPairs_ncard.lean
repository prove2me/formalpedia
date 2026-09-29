-- Prove2me | solution 1 for Bridges.ResidueLeakage.consistentPairs_ncard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:44:07.681667+00:00
-- url     : https://prove2.me/submissions/49d3e6d5-af51-46de-95bb-682b88037697

-- Sol generated from Bridges/ResidueLeakageTorsorTriviality.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageCounting
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Definitions.Def_Bridges_ResidueLeakageTorsorTriviality
import Theorems.Thm_Bridges_ResidueLeakage_consistentPairs_eq
import Theorems.Thm_Bridges_ResidueLeakage_signVectors_ncard
/-
# The consistent factor-fingerprint set is a trivial torsor (conjecture C5, closed)

Eighth file of the residue-leakage thread.  The previous files show that the QR
fingerprint prunes nothing (`dirichlet_no_pruning`), that all `2^K` patterns
occur (`qrFingerprint_pattern_surjective`), and that consistency of a pair of
primes with the observation is *exactly* the symmetric relation
`(a|q) = (a|N₀)·(a|p)` (`consistent_iff_product_constraint`).

Conjecture C5 of `FUTURE_DIRECTIONS.md` asked for the structural reformulation:
the "factorisation fibre"

`Φ(N₀) = { (F_A(p), F_A(q)) : p, q prime, F_A(p·q) = F_A(N₀) }`

should be a *trivial torsor* under the anti-diagonal
`Δ⁻ = { (w, w) : w ∈ {±1}^K }`, and this triviality should be equivalent to the
no-pruning statement.  This file proves it:

* `consistentPairs_eq` — the fibre is precisely the graph of the translation
  `u ↦ F_A(N₀) · u`, i.e. a coset of `Δ⁻` in `{±1}^K × {±1}^K`;
* `consistentPairs_simply_transitive` — `Δ⁻` acts *simply transitively* on the
  fibre (existence **and** uniqueness of the connecting sign vector): the fibre
  has trivial monodromy, so it is a trivial `Δ⁻`-torsor;
* `consistentPairs_fst_eq` — the fibre projects **onto** all of `{±1}^K` in the
  first coordinate, which is the no-pruning theorem in torsor form;
* `consistentPairs_ncard` — the fibre has exactly `2^K` elements, i.e. the
  residue channel leaves exactly the full `K` free bits of `F_A(p)`.

Everything is proved for an arbitrary duplicate-free list `A` of probe primes.
-/


open Bridges.ResidueLeakage

/-! ## Pointwise multiplication of sign vectors -/




/-! ## Bookkeeping: symbols of a prime outside the probe set -/



/-! ## The factorisation fibre -/



/-! ## Trivial monodromy: the anti-diagonal acts simply transitively -/


/-! ## Torsor form of the no-pruning theorem, and the exact size of the fibre -/





open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    (hnd : A.Nodup) {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a) :
    (consistentPairs A N₀).ncard = 2 ^ A.length := by
  have himg : consistentPairs A N₀ =
      (fun u => (u, signMul (qrFingerprint A N₀) u)) '' signVectors A.length := by
    rw [consistentPairs_eq hA hnd hN₀ hNA]
    ext ⟨u, v⟩
    constructor
    · rintro ⟨hu, hv⟩
      dsimp only at hu hv
      subst hv
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u', hu', h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
      exact ⟨hu', rfl⟩
  have hinj : Function.Injective
      (fun u => (u, signMul (qrFingerprint A N₀) u)) := by
    intro a b hab
    simpa using congrArg Prod.fst hab
  rw [himg, Set.ncard_image_of_injective _ hinj, signVectors_ncard]
