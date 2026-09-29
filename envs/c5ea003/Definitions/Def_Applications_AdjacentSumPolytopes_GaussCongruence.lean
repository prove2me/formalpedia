-- Prove2me | Definitions.Def_Applications_AdjacentSumPolytopes_GaussCongruence
-- name    : Applications_AdjacentSumPolytopes_GaussCongruence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:27:04.699761+00:00
-- url     : https://prove2.me/theorems/5b4ad69e-344d-4c66-b9ac-2b970d8c6fd5
-- title:
--   Aether Catalog definitions — Applications_AdjacentSumPolytopes_GaussCongruence
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AdjacentSumPolytopes.GaussCongruence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AdjacentSumPolytopes/GaussCongruence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace

/-!
# The full Gauss congruence for the adjacent-sum transfer matrix

`Applications.AdjacentSumPolytopes.Necklace` proved the Gauss congruence
`p ∣ tr(Mᵖ) − tr(M)` for *prime* lengths, using the `p`-group fixed point formula, and
left the general case as a conjecture.  Here we settle it:

`n ∣ ∑_{d ∣ n} μ(n/d) · tr(Mⁿ)`   for every `n ≥ 1`,

where `M = adjMat s` is the adjacent-sum transfer matrix.  Equivalently the *primitive*
cyclic counts `primCyc s n` — the Möbius transform of the trace sequence — count the
aperiodic cyclic adjacent-sum words, hence are divisible by their length.

The proof is the necklace argument, made precise:

* `cycExt` extends a cyclic word of length `e + 1` periodically to a cyclic word of
  length `q + 1` whenever `(e+1) ∣ (q+1)`; it is injective, rotation-equivariant, and its
  image is exactly the set of `(e+1)`-periodic words (`cycExt_surjective_on_periodic`);
* therefore the number of length-`(q+1)` words of *exact* period `d` equals the number of
  *aperiodic* words of length `d` (`card_minimalPeriod_eq_aper`);
* the abstract orbit-peeling lemma of `Applications.AdjacentSumPolytopes.Periodicity`
  gives `d ∣ aperCyc s d`, and Möbius inversion identifies `aperCyc s n = primCyc s n`.

-- !-- Lab Notes -- !--
* **Hypothesis.** `primCyc s n` counts aperiodic cyclic adjacent-sum words of length `n`,
  hence `n ∣ primCyc s n` for all `n ≥ 1`, not only for `n` prime.
* **Experiment.** `s = 2`, trace sequence `tr(Mⁿ) = 2, 6, 11, 26, 57, 129, 289` for
  `n = 1..7`.  Möbius transforms: `primCyc 1 = 2`, `primCyc 2 = 6 - 2 = 4`,
  `primCyc 3 = 11 - 2 = 9`, `primCyc 4 = 26 - 6 = 20`, `primCyc 6 = 129 - 11 - 6 + 2 = 114`.
  Divisibility: `1∣2`, `2∣4`, `3∣9`, `4∣20`, `6∣114 = 6·19`.  The composite cases `4` and
  `6` are exactly the ones the prime-only argument could not reach.
* **Analysis.** The obstruction in the previous cycle was that the `p`-group fixed-point
  theorem only sees prime lengths.  Replacing it by the exact-period decomposition
  removes the arithmetic hypothesis entirely: the only input is that rotation is an
  injective map with `rot^[n] = id`.
* **Critique.** The argument nowhere assumes the alphabet nonempty or the constraint
  nontrivial; the degenerate readings are still true statements, and for `s ≥ 0` the
  counts are positive (the all-zero word is always admissible), so the congruence is not
  vacuous.
-/

namespace AdjSum

open Finset Function Matrix

/-- The residue index `m mod (e+1)` as an element of `Fin (e+1)`. -/
def idx (e m : ℕ) : Fin (e + 1) := ⟨m % (e + 1), Nat.mod_lt _ (Nat.succ_pos e)⟩



lemma idx_add_one (e m : ℕ) : idx e m + 1 = idx e (m + 1) := by
  refine Fin.ext ?_
  show (m % (e + 1) + (1 : Fin (e + 1)).val) % (e + 1) = (m + 1) % (e + 1)
  rw [Fin.val_one', ← Nat.add_mod]

/-- Auxiliary normalisation of `1 % (q+1)` modulo a divisor `e + 1` of `q + 1`. -/
lemma add_one_mod_dvd {e q : ℕ} (h : (e + 1) ∣ (q + 1)) (m : ℕ) :
    (m + 1 % (q + 1)) % (e + 1) = (m + 1) % (e + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have he : e = 0 := by
      have := Nat.le_of_dvd (by omega) h
      omega
    subst he
    simp
  · rw [Nat.mod_eq_of_lt (show 1 < q + 1 by omega)]

/-! ## Iterates of the rotation -/





/-! ## Periodic extension of cyclic words -/


/-- Periodic extension of a cyclic word of length `e + 1` to one of length `q + 1`. -/
def cycExt {s e q : ℕ} (h : (e + 1) ∣ (q + 1)) (y : CycPt s e) : CycPt s q :=
  ⟨fun i => y.1 (idx e i.val), by
    rw [mem_cycSet]
    intro i
    have hy := (mem_cycSet.mp y.2) (idx e i.val)
    have hkey : idx e ((i + 1).val) = idx e i.val + 1 := by
      rw [idx_add_one]
      refine Fin.ext ?_
      show ((i.val + (1 : Fin (q + 1)).val) % (q + 1)) % (e + 1) = (i.val + 1) % (e + 1)
      rw [Fin.val_one', Nat.mod_mod_of_dvd _ h, add_one_mod_dvd h]
    rw [hkey]
    exact hy⟩






/-! ## Exact-period counts -/

/-- The number of *aperiodic* cyclic adjacent-sum words of length `q + 1`. -/
noncomputable def aperCyc (s q : ℕ) : ℕ :=
  (Finset.univ.filter
    (fun x : CycPt s q => Function.minimalPeriod (rot s q) x = q + 1)).card




/-! ## The necklace decomposition of the trace sequence -/

/-- The aperiodic counts indexed by the *length* `n` (rather than by `n - 1`). -/
noncomputable def aperN (s n : ℕ) : ℕ := if n = 0 then 0 else aperCyc s (n - 1)








end AdjSum


