-- Prove2me | solution 1 for DialThreshold.exists_large_dial_fibre
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:56:20.567677+00:00
-- url     : https://prove2.me/submissions/c745e5a7-834e-447b-b263-0fcb1b73bfd0

-- Sol generated from Combinatorics/DialThresholdNoAmplification.lean
import Mathlib
import Definitions.Def_Combinatorics_DialThresholdNoAmplification
import Definitions.Def_Combinatorics_Round11FingerprintInformation
import Theorems.Thm_DialThreshold_card_image_dialVec_le
/-
# DIAL-THRESHOLD: residue dials cannot amplify a Coppersmith hint

Formal companion to `45_DialThreshold_NoAmplification.md` (experiment #380).

**The question.**  A Coppersmith-style attack starts from a *partial key hint*:
the residue `p % m` of the secret prime, with `m ≈ N^{1/4}`.  The "free witness"
side of the programme offers a different kind of data: a vector of **residue
dials** `p ↦ ((D₁ | p), …, (D_K | p))` of Kronecker symbols at fundamental
discriminants.  Each dial is a *periodic* function of `p`, with conductor
dividing `4|D_i|`.  Can the dials *amplify* the hint — cut the candidate set
below what `p % m` already achieves?

**The answer, proved here: no.**  Everything is controlled by one integer,
the conductor lcm `M* = lcm_i cond(D_i)`, measured against the hint modulus `m`:

* `DialThreshold.card_image_dialVec_le` — the **master bound**.  On any candidate
  set inside one hint class mod `m`, the dial vector takes at most
  `M* / gcd(M*, m)` distinct values.  This is the exact amplification budget.
* `DialThreshold.exists_large_dial_fibre` — consequently some dial reading keeps
  at least a `gcd(M*,m)/M*` fraction of the candidates: the dials cannot shrink
  the candidate set by more than the factor `M*/gcd(M*, m)`.
* **Regime 1 (`M* ∣ m`)**: `dialVec_const_of_dvd`, `dial_cut_trivial`,
  `zeroInfo_dialVec_of_dvd`, `zeroInfo_dialVec_postprocessed` — the budget is
  `1`: the dial vector is *constant* on the candidate set, the induced cut is the
  identity, and (in the exact counting sense `Round11.ZeroInfo` of the catalog)
  the dials carry **zero information** about any secret whatsoever, even after
  arbitrary post-processing.
* **Regime 2 (`M* ∤ m`)**: `hint_underdetermines_residue`,
  `not_hintComputable_of_separates`, `pinning_forces_not_dvd`,
  `card_le_of_dialVec_injOn` — a dial system that separates even two candidates
  is *not computable from the hint*, and pinning `C` candidates forces
  `M*/gcd(M*,m) ≥ C`, i.e. the dials must reach strictly beyond the hint.
* `DialThreshold.dial_capacity` — the information-theoretic side: `K` sign dials
  cannot separate more than `3^K` candidates, so pinning needs `K = Ω(log C)`.

Together these are a dichotomy: *hint-computable ⇒ information-useless*
(`no_amplification_of_hintComputable`), *informative ⇒ not hint-computable*.

The concluding section instantiates the two regimes on the experiment's own
numbers with genuine Kronecker dials `(D | ·)`:
`N = 808·10⁶`-scale hint `m = 168` with dials of conductor `12, 84, 168`
(Regime 1) and `N = 340·10⁶`-scale hint `m = 135` with the dial `(-4 | ·)` of
conductor `16` (Regime 2, witnessed by the candidate pair `541, 811`).
-/

open DialThreshold

open Finset

/-! ## 1. Residue dials -/


open Dial

variable (d : Dial)





/-! ### Kronecker dials

The free-witness dials of the experiment: `p ↦ (D | p)`, realized as a genuinely
periodic function by evaluating the Jacobi symbol at the reduced representative
modulo `4|D|`.  On odd candidates it agrees with `(D | ·)` on the nose. -/




/-! ## 2. Dial systems and the conductor lcm `M*` -/

variable {K : ℕ}







/-! ## 3. Counting the residues visible inside a hint class -/


/-! ## 4. The master bound: the amplification budget is `M* / gcd(M*, m)` -/



/-! ## 5. Regime 1 (`M* ∣ m`): the dials are constant, hence useless -/





/-! ## 6. Hint-computability, and the dichotomy -/









/-! ## 7. The information-theoretic side: `K = Ω(log C)` dials are needed -/



/-! ## 8. The two experimental regimes, on the experiment's own numbers -/



















/-! ## 9. The verdict

`no_amplification_dichotomy` packages the closure: for every dial system and
every hint modulus, either the dials are hint-computable — and then they are
provably worthless on the candidate set, for every secret and every
post-processing — or they are not computable from the hint at all. -/



open DialThreshold in
theorem solution(Ds : Fin K → Dial) (Ω : Finset ℕ) {m r : ℕ} (hm : 0 < m)
    (hΩ : ∀ p ∈ Ω, p % m = r % m) (hne : Ω.Nonempty) :
    ∃ v, Ω.card ≤ (condLcm Ds / Nat.gcd (condLcm Ds) m) *
        (Ω.filter (fun p => dialVec Ds p = v)).card := by
  classical
  set I := Ω.image (dialVec Ds) with hI
  have hIne : I.Nonempty := hne.image _
  obtain ⟨v, hvI, hvmax⟩ := Finset.exists_max_image I
    (fun v => (Ω.filter (fun p => dialVec Ds p = v)).card) hIne
  refine ⟨v, ?_⟩
  have hfib : Ω.card = ∑ w ∈ I, (Ω.filter (fun p => dialVec Ds p = w)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p hp => mem_image_of_mem _ hp)
  have hsum : ∑ w ∈ I, (Ω.filter (fun p => dialVec Ds p = w)).card
      ≤ I.card * (Ω.filter (fun p => dialVec Ds p = v)).card := by
    simpa [smul_eq_mul] using
      Finset.sum_le_card_nsmul I (fun w => (Ω.filter (fun p => dialVec Ds p = w)).card)
        _ (fun w hw => hvmax w hw)
  have hIcard : I.card ≤ condLcm Ds / Nat.gcd (condLcm Ds) m :=
    card_image_dialVec_le Ds Ω hm hΩ
  calc Ω.card = ∑ w ∈ I, (Ω.filter (fun p => dialVec Ds p = w)).card := hfib
    _ ≤ I.card * (Ω.filter (fun p => dialVec Ds p = v)).card := hsum
    _ ≤ (condLcm Ds / Nat.gcd (condLcm Ds) m) *
          (Ω.filter (fun p => dialVec Ds p = v)).card := Nat.mul_le_mul_right _ hIcard
