-- Prove2me | solution 1 for UniversalPosets.isUniversalPosetOfSize_five_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:30:00.007245+00:00
-- url     : https://prove2.me/submissions/fb1699a0-2a79-4495-8003-d25d1295be54

-- Sol generated from Cryptography/UniversalPosets/ExactSmall.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_MinSize

/-!
# A linear lower bound and the exact value `U(3) = 5`

This file continues the quantitative study of

`minUniversalSize n = U(n)` : the least number of points of a poset containing
every `n`-element poset as an induced subposet,

by closing two of the questions that the previous cycle could only answer with
machine evidence.

Proved here:

* `two_mul_sub_one_le_minUniversalSize` : `2n - 1 ≤ U(n)` for **every** `n`.
  The argument is a *structural* one, not a counting one: a universal host must
  contain an `n`-chain and an `n`-antichain, and these two `n`-sets can share at
  most one point, because two shared points would be simultaneously comparable
  (inside the chain) and incomparable (inside the antichain).  This is sharp at
  `n = 2` and `n = 3`.
* `minUniversalSize_three` : `U(3) = 5` **exactly**.  The upper bound is the
  explicit five-point host `host3Le` (a diamond `4 < 2, 3 < 1` together with an
  isolated point `0`); its universality for the nineteen partial orders on three
  points is decided by the kernel, and the matching lower bound `5 ≤ U(3)` is
  the case `n = 3` of the linear bound above.  In the previous cycle `U(3) = 5`
  was recorded as unverified computational evidence; it is now a theorem.
* `minUniversalSize_mono` : `U` is monotone, so all lower bounds propagate
  upwards.
* `minUniversalSize_zero`, `minUniversalSize_one` : `U(0) = 0`, `U(1) = 1`.

Together with `two_pow_le_minUniversalSize_sq` (`2^{n/4} ≤ U(n)`) and
`minUniversalSize_le_two_pow` (`U(n) ≤ 2^n`) this gives
`max (2n-1, 2^{n/4}) ≤ U(n) ≤ 2^n`, with equality in the lower bound for
`n ≤ 3`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  The counting bound `2^{n/4}` is useless for small
`n` (it gives `2` at `n = 2`), yet the true values `1, 3, 5` grow linearly with
slope `2`.  Conjecture: the *chain versus antichain* obstruction alone forces
slope `2`, i.e. `U(n) ≥ 2n - 1`, and this is tight for `n ≤ 3`.

Experiment (Experimenter).  An exhaustive search over the `4231` partial orders
on five points found `300` hosts universal for the `19` partial orders on three
points, and none on four points; one of the `300` with the fewest relations is
the diamond-plus-isolated-point host formalised here as `host3Le`.  Its
universality is re-verified inside Lean by `decide` (512 Boolean relations, 125
candidate embeddings), so no trust is placed in the external search.

Analysis (Analyst).  The chain/antichain argument explains *why* no four-point
host exists, without any search: a four-point host with a three-chain has at
most two points off that chain, so it cannot contain three pairwise
incomparable points.  The same argument scales to all `n`, which is what
`two_mul_sub_one_le_minUniversalSize` records.  The bound is not tight for large
`n`, where the exponential counting bound takes over; the crossover is around
`n = 20`.

Critique (Critic).  Nothing here is vacuous: `IsUniversalPosetOfSize 5 3` is
witnessed by an explicit relation, the lower bound is proved for an arbitrary
host, and the two bounds meet.  The kernel-checked `decide` calls are on genuine
finite search problems (they are not `native_decide`), and every hypothesis of
the abstract lemmas is discharged for the concrete host.
-/

open UniversalPosets

open Function

/-! ## Equality as a partial order -/


/-! ## The chain-versus-antichain lower bound -/

/-! ## Overlap of two induced copies -/








/-! ## Monotonicity of `U` -/





/-! ## The exact values `U(0) = 0`, `U(1) = 1` -/



/-! ## The five-point host and `U(3) = 5` -/


theorem host3Le_refl (x : Fin 5) : host3Le x x = true := by revert x; decide

theorem host3Le_trans (x y z : Fin 5) (h1 : host3Le x y = true) (h2 : host3Le y z = true) :
    host3Le x z = true := by revert x y z; decide

theorem host3Le_antisymm (x y : Fin 5) (h1 : host3Le x y = true) (h2 : host3Le y x = true) :
    x = y := by revert x y; decide

set_option maxRecDepth 10000 in
/--
**Kernel-checked universality of the five-point host.**  Every partial order on
three points (given here in Boolean form) embeds as an induced subposet.
-/
theorem host3Le_universal_bool (R : Fin 3 → Fin 3 → Bool)
    (hrefl : ∀ x, R x x = true)
    (htrans : ∀ x y z, R x y = true → R y z = true → R x z = true)
    (hanti : ∀ x y, R x y = true → R y x = true → x = y) :
    ∃ f : Fin 3 → Fin 5, ∀ x y, host3Le (f x) (f y) = R x y := by
  revert R
  decide






open UniversalPosets in
theorem solution: IsUniversalPosetOfSize 5 3 := by
  classical
  refine ⟨fun a b => host3Le a b = true, ?_, ?_⟩
  · exact
      haveI : Std.Refl (fun a b : Pt 5 => host3Le a b = true) := ⟨host3Le_refl⟩
      haveI : IsTrans (Pt 5) (fun a b : Pt 5 => host3Le a b = true) :=
        ⟨fun a b c => host3Le_trans a b c⟩
      haveI : IsPreorder (Pt 5) (fun a b : Pt 5 => host3Le a b = true) := ⟨⟩
      haveI : Std.Antisymm (fun a b : Pt 5 => host3Le a b = true) :=
        ⟨fun a b => host3Le_antisymm a b⟩
      ⟨⟩
  · intro r hr
    obtain ⟨f, hf⟩ := host3Le_universal_bool (fun x y => decide (r x y))
      (fun x => by simpa using refl_of r x)
      (fun x y z h1 h2 => by
        simp only [decide_eq_true_eq] at *
        exact trans_of r h1 h2)
      (fun x y h1 h2 => by
        simp only [decide_eq_true_eq] at *
        exact antisymm_of r h1 h2)
    refine ⟨f, fun x y => ?_⟩
    show host3Le (f x) (f y) = true ↔ r x y
    rw [hf x y, decide_eq_true_eq]
