-- Prove2me | solution 1 for UniversalPosets.exists_code
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:28:40.094458+00:00
-- url     : https://prove2.me/submissions/260c6f51-32fc-47d2-8e8e-353da11cecf6

-- Sol generated from Cryptography/UniversalPosets/FourPoints.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_FourPoints
import Definitions.Def_Cryptography_UniversalPosets_StrictMono

/-!
# Four points: `U(4) ≤ 8`

`ExactSmall.lean` proved `U(3) = 5` and the general bound `2n - 1 ≤ U(n)`, which
gives `7 ≤ U(4)`.  This file adds the matching upper bound `U(4) ≤ 8` by
exhibiting an explicit eight-point host and *kernel-checking* that every one of
the `219` partial orders on four points embeds into it as an induced subposet.
Hence

`7 ≤ U(4) ≤ 8`.

## How the verification is organised

Deciding a statement quantified over the function type `Fin 4 → Fin 4 → Bool`
is hopeless for the kernel (the `Fintype` instance for a function type builds a
`Finset` of `65536` functions with quadratic deduplication).  Instead:

* a partial order on `Fin 4` is encoded by the `12` bits of its off-diagonal
  entries, i.e. by a natural number `m < 4096` (`relOf`, `idx4`, `pr4`);
* the embedding of the poset coded by `m` is *precomputed*: `emb4Of m` looks the
  witness up in the table `tbl4` (found by an external search, but re-verified
  here — nothing is trusted about the way the table was produced);
* the verification `host4_universal_chunk` is a single `decide +kernel` over
  `m = 64a + b` with `a, b < 64`, which keeps the kernel's recursion depth low;
* `Nat.ofBits` turns an arbitrary partial order on `Fin 4` back into a code, so
  the abstract statement `IsUniversalPosetOfSize 8 4` follows.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  The values `U(1), U(2), U(3) = 1, 3, 5` and the bound
`2n-1 ≤ U(n)` suggest `U(n) = 2n - 1`; the first test is `n = 4`.

Experiment (Experimenter).  An exhaustive search over the `96428` naturally
labelled seven-point posets found **no** seven-point host for the four-element
posets, while a randomised search found eight-point hosts; the sparsest one
found is the host `host4Le` used here.  The upper bound `U(4) ≤ 8` is proved
below; the lower bound `U(4) ≥ 8` (i.e. the nonexistence part) is *not* claimed
as a theorem, since replaying that search inside the kernel is infeasible.

Analysis (Analyst).  So `U(4) ∈ {7, 8}`, with computational evidence for `8`.
This already falsifies the naive guess `U(n) = 2n-1` if the evidence is correct,
and it is the first place where the structural bound stops being sharp.

Critique (Critic).  The `decide +kernel` call is a genuine finite verification
(no `native_decide`): it checks all `4096` codes, filters the `219` that are
partial orders, and verifies the tabulated embedding for each of them.  The
bridge from `IsUniversalPosetOfSize` to the coded statement is proved, not
assumed, so a wrong table would make the file fail to compile.
-/

open UniversalPosets

/-! ## The eight-point host -/






/-! ## Coding partial orders on four points by twelve bits -/









/-! ## The kernel verification -/



/-! ## From codes back to abstract posets -/





open UniversalPosets in
open Classical in
theorem solution(r : Fin 4 → Fin 4 → Prop) (hr : IsPartialOrder (Fin 4) r) :
    ∃ m < 4096, ∀ i j : Fin 4, relOf m i j = decide (r i j) := by
  refine ⟨Nat.ofBits (fun k : Fin 12 => decide (r (pr4 k).1 (pr4 k).2)), ?_, ?_⟩
  · have h := Nat.ofBits_lt_two_pow (fun k : Fin 12 => decide (r (pr4 k).1 (pr4 k).2))
    norm_num at h
    exact h
  · have hrefl : ∀ i : Fin 4, decide (r i i) = true := fun i => decide_eq_true (refl_of r i)
    have hreflP : ∀ i : Fin 4, r i i := fun i => refl_of r i
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [relOf, idx4, Nat.testBit_ofBits] <;>
      first
        | rfl
        | simp [hreflP]
        | norm_num [pr4, hrefl]
