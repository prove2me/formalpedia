-- Prove2me | Definitions.Def_Erdos249257_TotientMahlerDefect
-- name    : Erdos249257_TotientMahlerDefect
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T13:46:21.717092+00:00
-- url     : https://prove2.me/theorems/00234121-9077-4cb1-a3c6-d5df2db01452
-- title:
--   Dyadic totient kernel and canonical families
-- statement:
--   Defines dyadic totient sections and canonical families, with source proofs of independence, finite-level rank, and an infinite relation structure. These are structural results and do not prove irrationality of the totient series.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/TotientMahlerDefect.lean#L36-L56
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/TotientMahlerDefect.lean#L927-L1000
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/TotientMahlerDefect.lean#L1069-L1090

import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Exact ranks of dyadic totient kernels

For `K_{j,r}(n) = φ(2^j n + r)`, this module proves two unconditional rank
statements relevant to Erdős #249:

* the complete kernel through every positive level `e` has dimension
  exactly `2^e+1` over `ℚ`;
* the kernel containing all dyadic levels is infinite-dimensional.

The proof first removes the repeated even-residue channels.  It then proves
linear independence of the remaining canonical family by constructing a
nonzero evaluation minor: CRT and Dirichlet's theorem make one affine channel
prime while forcing a fresh prime divisor in every other channel.  The exact
rank of the complete truncation follows because the removed channels reduce
recursively to lower-level canonical channels.

These are structural theorems about Euler's totient sequence, not a proof that
the totient series is irrational.  A rationality argument would still have to
produce a finite-rank compression, or an equivalent contradiction object,
from the assumed rationality of that series.
-/

namespace Erdos249257

open Module Matrix













/-- Pull a finite family of sequences back along a finite family of evaluation
points. -/
def evaluationLinearMap {ι : Type*} [Fintype ι] (rowIndex : ι → ℕ) :
    (ℕ → ℚ) →ₗ[ℚ] (ι → ℚ) where
  toFun f i := f (rowIndex i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A square nonzero evaluation minor.  This is the exact finite object needed
to turn number-theoretic row construction into linear independence. -/
structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) where
  rowIndex : ι → ℕ
  det_ne_zero :
    Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0

/-- A nonzero square evaluation minor proves that the underlying functions are
linearly independent. -/
theorem linearIndependent_of_separatedMinorCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (family : ι → ℕ → ℚ)
    (cert : SeparatedMinorCertificate family) :
    LinearIndependent ℚ family := by
  apply LinearIndependent.of_comp (evaluationLinearMap cert.rowIndex)
  change LinearIndependent ℚ (fun j i => family j (cert.rowIndex i))
  exact Matrix.linearIndependent_cols_of_det_ne_zero cert.det_ne_zero















/-! ## The normalized odd-input affine family -/









































/-- A nonzero affine slope has a root modulo any larger prime. -/
theorem exists_affine_root_mod_prime {a r q : ℕ}
    (ha : 0 < a) (haq : a < q) (hq : q.Prime) :
    ∃ x < q, q ∣ a * x + r := by
  have hnot : ¬q ∣ a := Nat.not_dvd_of_pos_of_lt ha haq
  have hac : a.Coprime q := (hq.coprime_iff_not_dvd.mpr hnot).symm
  obtain ⟨x, hxlt, hx⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (q - r % q) hac hq.ne_zero
  refine ⟨x, hxlt, ?_⟩
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hx]
  have hrlt : r % q < q := Nat.mod_lt _ hq.pos
  by_cases hrzero : r % q = 0
  · simp [hrzero]
  · have hsub : q - r % q < q := Nat.sub_lt hq.pos (Nat.pos_of_ne_zero hrzero)
    rw [Nat.mod_eq_of_lt hsub, Nat.sub_add_cancel hrlt.le, Nat.mod_self]

/-- If one affine value vanishes modulo a prime and the cross determinant is
nonzero and smaller than that prime, then the other affine value is coprime to
the prime. -/
theorem affine_target_coprime_of_cross
    {ai ri aj rj q n : ℕ}
    (hq : q.Prime)
    (hcross : aj * ri ≠ ai * rj)
    (hleft : aj * ri < q) (hright : ai * rj < q)
    (hoff : q ∣ aj * n + rj) :
    (ai * n + ri).Coprime q := by
  apply (hq.coprime_iff_not_dvd.mpr ?_).symm
  intro htarget
  have ht0 : ai * n + ri ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr htarget
  have hj0 : aj * n + rj ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hoff
  have hsum : aj * ai * n + aj * ri ≡ aj * ai * n + ai * rj [MOD q] := by
    have hleft0 := ht0.mul_left aj
    have hright0 := hj0.mul_left ai
    convert hleft0.trans hright0.symm using 1 <;> ring
  have hcrossMod : aj * ri ≡ ai * rj [MOD q] :=
    Nat.ModEq.add_left_cancel' (aj * ai * n) hsum
  exact hcross (hcrossMod.eq_of_lt_of_lt hleft hright)









/-! ## A parity-separated determinant kernel -/











/-! ## The exact rank of the complete finite truncation -/









/-! ## The full dyadic kernel is infinite-dimensional -/




















/-! ## An explicit basis for the span of every dyadic section

The finite-level theorems above already determine the whole linear-relation
structure of the dyadic sections of `φ`, because linear independence has finite
character.  Assembling them gives one *infinite* linearly independent family --
the two zero-residue channels `n ↦ φ(n)`, `n ↦ φ(2n)` together with one channel
`n ↦ φ(2^(j+1) n + 2r+1)` for every odd residue at every level -- which by
`totientKernel_zero_residue` and `totientKernel_even_residue_reduce` spans every
remaining dyadic section.  It is therefore a basis of the span of the full
dyadic kernel, which is strictly sharper than the infinite-dimensionality
statement above: it says that the only `ℚ`-linear relations among dyadic
sections of `φ` are the ones generated by those two elementary identities.

This is a theorem about `φ`, not about `∑ φ(n)/2ⁿ`.  It proves no irrationality
statement and leaves the rationality-side finite-rank compression theorem
untouched. -/






























end Erdos249257


