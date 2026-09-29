-- Prove2me | solution 1 for UniversalPosets.isUniversalPosetOfSize_eight_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:29:59.475904+00:00
-- url     : https://prove2.me/submissions/09304f52-a87d-42fc-9546-b0ed92080d50

-- Sol generated from Cryptography/UniversalPosets/FourPoints.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_FourPoints
import Definitions.Def_Cryptography_UniversalPosets_MinSize
import Definitions.Def_Cryptography_UniversalPosets_StrictMono
import Theorems.Thm_UniversalPosets_exists_code

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



theorem host4Le_refl (x : Fin 8) : host4Le x x = true := by revert x; decide

theorem host4Le_trans (x y z : Fin 8) (h1 : host4Le x y = true) (h2 : host4Le y z = true) :
    host4Le x z = true := by revert x y z; decide

theorem host4Le_antisymm (x y : Fin 8) (h1 : host4Le x y = true) (h2 : host4Le y x = true) :
    x = y := by revert x y; decide

/-! ## Coding partial orders on four points by twelve bits -/









/-! ## The kernel verification -/

set_option maxRecDepth 100000 in
/--
**Kernel check.**  Written with `m = 64a + b` to keep the kernel's recursion
shallow: for every code `m < 4096` of a partial order on four points, the
tabulated map is an induced embedding into the host.
-/
theorem host4_universal_chunk : ∀ a < 64, ∀ b < 64, isPO4 (64 * a + b) →
    ∀ i j : Fin 4, host4Le (emb4 (emb4Of (64 * a + b)) i) (emb4 (emb4Of (64 * a + b)) j)
      = relOf (64 * a + b) i j := by
  decide +kernel

theorem host4_universal_code (m : Nat) (hm : m < 4096) (hpo : isPO4 m) (i j : Fin 4) :
    host4Le (emb4 (emb4Of m) i) (emb4 (emb4Of m) j) = relOf m i j := by
  have hchunk := host4_universal_chunk (m / 64) (by omega) (m % 64) (by omega)
  rw [show 64 * (m / 64) + m % 64 = m by omega] at hchunk
  exact hchunk hpo i j

/-! ## From codes back to abstract posets -/





open UniversalPosets in
theorem solution: IsUniversalPosetOfSize 8 4 := by
  classical
  refine ⟨fun a b => host4Le a b = true, ?_, ?_⟩
  · exact
      haveI : Std.Refl (fun a b : Pt 8 => host4Le a b = true) := ⟨host4Le_refl⟩
      haveI : IsTrans (Pt 8) (fun a b : Pt 8 => host4Le a b = true) :=
        ⟨fun a b c => host4Le_trans a b c⟩
      haveI : IsPreorder (Pt 8) (fun a b : Pt 8 => host4Le a b = true) := ⟨⟩
      haveI : Std.Antisymm (fun a b : Pt 8 => host4Le a b = true) :=
        ⟨fun a b => host4Le_antisymm a b⟩
      ⟨⟩
  · intro r hr
    obtain ⟨m, hmlt, key⟩ := exists_code r hr
    have hpo : isPO4 m := by
      constructor
      · intro i j k h1 h2
        rw [key] at h1 h2 ⊢
        simp only [decide_eq_true_eq] at h1 h2 ⊢
        exact trans_of r h1 h2
      · intro i j h1 h2
        rw [key] at h1 h2
        simp only [decide_eq_true_eq] at h1 h2
        exact antisymm_of r h1 h2
    refine ⟨fun i => emb4 (emb4Of m) i, fun x y => ?_⟩
    show host4Le (emb4 (emb4Of m) x) (emb4 (emb4Of m) y) = true ↔ r x y
    rw [host4_universal_code m hmlt hpo x y, key x y, decide_eq_true_eq]
