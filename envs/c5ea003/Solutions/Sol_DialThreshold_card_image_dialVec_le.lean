-- Prove2me | solution 1 for DialThreshold.card_image_dialVec_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:54:51.76634+00:00
-- url     : https://prove2.me/submissions/5667f40d-ff85-41b1-a26d-48dcda128d8b

-- Sol generated from Combinatorics/DialThresholdNoAmplification.lean
import Mathlib
import Definitions.Def_Combinatorics_DialThresholdNoAmplification
import Definitions.Def_Combinatorics_Round11FingerprintInformation
import Theorems.Thm_DialThreshold_Dial_chi_congr
import Theorems.Thm_DialThreshold_card_filter_range_mod
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



theorem cond_dvd_condLcm (Ds : Fin K → Dial) (i : Fin K) : (Ds i).cond ∣ condLcm Ds :=
  Finset.dvd_lcm (mem_univ i)

theorem condLcm_pos (Ds : Fin K → Dial) : 0 < condLcm Ds := by
  refine Nat.pos_of_ne_zero (fun h => ?_)
  rw [condLcm, Finset.lcm_eq_zero_iff] at h
  obtain ⟨i, -, hi⟩ := h
  exact absurd hi (Ds i).cond_pos.ne'

/-- `M*` is the exact resolution of a dial system: candidates congruent mod any
multiple of `M*` are indistinguishable by the dials. -/
theorem dialVec_congr (Ds : Fin K → Dial) {M a b : ℕ} (hM : condLcm Ds ∣ M)
    (h : a % M = b % M) : dialVec Ds a = dialVec Ds b :=
  funext fun i => (Ds i).chi_congr ((cond_dvd_condLcm Ds i).trans hM) h

/-- Special case: the dial vector is determined by the residue mod `M*`. -/
theorem dialVec_mod (Ds : Fin K → Dial) (p : ℕ) :
    dialVec Ds (p % condLcm Ds) = dialVec Ds p :=
  dialVec_congr Ds dvd_rfl (Nat.mod_mod_of_dvd p dvd_rfl)

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
    (hΩ : ∀ p ∈ Ω, p % m = r % m) :
    (Ω.image (dialVec Ds)).card ≤ condLcm Ds / Nat.gcd (condLcm Ds) m := by
  classical
  set M := condLcm Ds with hM
  set g := Nat.gcd M m with hgdef
  have hMpos : 0 < M := condLcm_pos Ds
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have hgM : g ∣ M := Nat.gcd_dvd_left _ _
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  set T := (range M).filter (fun x => x % g = r % g) with hT
  have hsub : Ω.image (dialVec Ds) ⊆ T.image (dialVec Ds) := by
    intro v hv
    rw [mem_image] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    refine mem_image.2 ⟨p % M, ?_, dialVec_mod Ds p⟩
    rw [hT, mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ hMpos, ?_⟩
    rw [Nat.mod_mod_of_dvd p hgM]
    exact (Nat.ModEq.of_dvd hgm (hΩ p hp))
  calc (Ω.image (dialVec Ds)).card ≤ (T.image (dialVec Ds)).card := card_le_card hsub
    _ ≤ T.card := card_image_le
    _ = M / g := card_filter_range_mod hgpos hgM (Nat.mod_lt _ hgpos)
