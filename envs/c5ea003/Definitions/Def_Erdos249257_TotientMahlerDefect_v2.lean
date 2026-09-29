-- Prove2me | Definitions.Def_Erdos249257_TotientMahlerDefect_v2
-- name    : Erdos249257_TotientMahlerDefect_v2
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T00:47:28.115578+00:00
-- url     : https://prove2.me/theorems/a519868c-5c02-41bc-82cd-19bd0dac6c4d
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

/-- The `(j,r)` dyadic-kernel channel of Euler's totient, viewed over `ℚ`. -/
def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

/-- The canonical channels through level `e`: the two zero-residue base
channels, followed by every odd residue at levels `1,...,e`. -/
abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)

/-- The canonical family indexed without duplicate even-residue channels. -/
def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)

/-- Every dyadic totient channel at levels `0,...,e`, before removing the
even-residue repetitions. -/
abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

/-- The complete finite dyadic kernel through level `e`. -/
def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val



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





/-- Totient of an odd number multiplied by a positive power of two. -/
theorem totient_two_pow_succ_mul_of_odd (t m : ℕ) (hm : Odd m) :
    Nat.totient (2 ^ (t + 1) * m) = 2 ^ t * Nat.totient m := by
  induction t with
  | zero =>
      simpa using Nat.totient_two_mul_of_odd hm
  | succ t ih =>
      have heven : Even (2 ^ (t + 1) * m) := by
        refine Even.mul_right ?_ m
        exact ⟨2 ^ t, by ring⟩
      calc
        Nat.totient (2 ^ (t + 1 + 1) * m) =
            Nat.totient (2 * (2 ^ (t + 1) * m)) := by
              congr 1
              ring
        _ = 2 * Nat.totient (2 ^ (t + 1) * m) :=
          Nat.totient_two_mul_of_even heven
        _ = 2 * (2 ^ t * Nat.totient m) := by rw [ih]
        _ = 2 ^ (t + 1) * Nat.totient m := by ring

/-- Repeated doubling scales the totient once the argument is already even. -/
theorem totient_two_pow_mul_two (j n : ℕ) :
    Nat.totient (2 ^ j * (2 * n)) =
      2 ^ j * Nat.totient (2 * n) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have heven : Even (2 ^ j * (2 * n)) := by
        exact Even.mul_left (by simp) _
      calc
        Nat.totient (2 ^ (j + 1) * (2 * n)) =
            Nat.totient (2 * (2 ^ j * (2 * n))) := by
              congr 1
              ring
        _ = 2 * Nat.totient (2 ^ j * (2 * n)) :=
          Nat.totient_two_mul_of_even heven
        _ = 2 * (2 ^ j * Nat.totient (2 * n)) := by rw [ih]
        _ = 2 ^ (j + 1) * Nat.totient (2 * n) := by ring

/-- Every positive zero-residue channel is a scalar multiple of the first
zero-residue channel. -/
theorem totientKernel_zero_residue (j n : ℕ) :
    totientKernelSeq (j + 1) 0 n =
      (2 ^ j : ℚ) * totientKernelSeq 1 0 n := by
  simp only [totientKernelSeq, add_zero]
  norm_cast
  rw [show 2 ^ (j + 1) * n = 2 ^ j * (2 * n) by ring]
  exact totient_two_pow_mul_two j n

/-- Exact reduction of an even residue to its odd-core channel. -/
theorem totientKernel_even_residue_reduce
    (j t s n : ℕ) (ht : t + 1 < j) (hs : Odd s) :
    totientKernelSeq j (2 ^ (t + 1) * s) n =
      (2 ^ t : ℚ) * totientKernelSeq (j - (t + 1)) s n := by
  simp only [totientKernelSeq]
  norm_cast
  have hpow : 2 ^ j = 2 ^ (t + 1) * 2 ^ (j - (t + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [show 2 ^ j * n + 2 ^ (t + 1) * s =
      2 ^ (t + 1) * (2 ^ (j - (t + 1)) * n + s) by
        rw [hpow]
        ring]
  apply totient_two_pow_succ_mul_of_odd
  have hevenPow : Even (2 ^ (j - (t + 1))) := by
    refine ⟨2 ^ (j - (t + 1) - 1), ?_⟩
    have hjt : 0 < j - (t + 1) := by omega
    calc
      2 ^ (j - (t + 1)) = 2 ^ ((j - (t + 1) - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (j - (t + 1) - 1) + 2 ^ (j - (t + 1) - 1) := by
        rw [pow_succ]
        ring
  exact (hevenPow.mul_right n).add_odd hs



/-! ## The normalized odd-input affine family -/

/-- On odd inputs the two zero channels coincide.  Before separating those
two columns at one even input, we work with the zero channel together with all
odd-residue affine channels. -/
abbrev TotientAffineIndex (e : ℕ) :=
  Option (Σ j : Fin e, Fin (2 ^ j.val))

/-- Slope of a normalized affine totient channel. -/
def totientAffineSlope {e : ℕ} : TotientAffineIndex e → ℕ
  | none => 1
  | some ⟨j, _⟩ => 2 ^ (j.val + 1)

/-- Residue of a normalized affine totient channel. -/
def totientAffineResidue {e : ℕ} : TotientAffineIndex e → ℕ
  | none => 0
  | some ⟨_, r⟩ => 2 * r.val + 1

/-- The natural-valued normalized affine channel. -/
def totientAffineValue {e : ℕ} (i : TotientAffineIndex e) (n : ℕ) : ℕ :=
  totientAffineSlope i * n + totientAffineResidue i



/-- The same normalized channels, parameterized by all odd inputs. -/
def totientAffineOddFamily (e : ℕ) : TotientAffineIndex e → ℕ → ℚ := fun i m =>
  Nat.totient (totientAffineValue i (2 * m + 1))

theorem totientAffineSlope_pos {e : ℕ} (i : TotientAffineIndex e) :
    0 < totientAffineSlope i := by
  cases i with
  | none => simp [totientAffineSlope]
  | some i => simp [totientAffineSlope]

theorem totientAffineResidue_lt_slope {e : ℕ} (i : TotientAffineIndex e) :
    totientAffineResidue i < totientAffineSlope i := by
  cases i with
  | none => simp [totientAffineSlope, totientAffineResidue]
  | some i =>
      rcases i with ⟨j, r⟩
      simp only [totientAffineSlope, totientAffineResidue]
      rw [pow_succ]
      omega

theorem totientAffineSlope_coprime_residue {e : ℕ} (i : TotientAffineIndex e) :
    (totientAffineSlope i).Coprime (totientAffineResidue i) := by
  cases i with
  | none => simp [totientAffineSlope, totientAffineResidue]
  | some i =>
      rcases i with ⟨j, r⟩
      simp only [totientAffineSlope, totientAffineResidue]
      exact (by simp : Odd (2 * r.val + 1)).coprime_two_left.pow_left (j.val + 1)

/-- The slope-residue pair uniquely identifies a normalized channel. -/
theorem totientAffine_parameters_injective (e : ℕ) :
    Function.Injective (fun i : TotientAffineIndex e =>
      (totientAffineSlope i, totientAffineResidue i)) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j =>
          rcases j with ⟨j, r⟩
          have := congrArg Prod.snd hij
          simp [totientAffineResidue] at this
  | some i =>
      rcases i with ⟨i, r⟩
      cases j with
      | none =>
          have := congrArg Prod.snd hij
          simp [totientAffineResidue] at this
      | some j =>
          rcases j with ⟨j, s⟩
          have hslope := congrArg Prod.fst hij
          have hresidue := congrArg Prod.snd hij
          simp only [totientAffineSlope] at hslope
          simp only [totientAffineResidue] at hresidue
          have hijval : i.val = j.val := by
            have := (Nat.pow_right_injective (a := 2) (by omega : 2 ≤ 2)) hslope
            omega
          have hijfin : i = j := Fin.ext hijval
          subst j
          have hrs : r.val = s.val := by omega
          have hrsfin : r = s := Fin.ext hrs
          exact congrArg (fun x => some (Sigma.mk i x)) hrsfin

/-- Distinct normalized affine channels have nonzero cross determinant. -/
theorem totientAffine_cross_ne {e : ℕ} {i j : TotientAffineIndex e} (hij : i ≠ j) :
    totientAffineSlope j * totientAffineResidue i ≠
      totientAffineSlope i * totientAffineResidue j := by
  intro hcross
  have hai : totientAffineSlope i ∣ totientAffineSlope j := by
    apply (totientAffineSlope_coprime_residue i).dvd_of_dvd_mul_right
    exact ⟨totientAffineResidue j, hcross⟩
  have haj : totientAffineSlope j ∣ totientAffineSlope i := by
    apply (totientAffineSlope_coprime_residue j).dvd_of_dvd_mul_right
    exact ⟨totientAffineResidue i, hcross.symm⟩
  have haslope : totientAffineSlope i = totientAffineSlope j :=
    Nat.dvd_antisymm hai haj
  have ha_pos := totientAffineSlope_pos i
  have hresidue : totientAffineResidue i = totientAffineResidue j := by
    rw [← haslope] at hcross
    apply Nat.eq_of_mul_eq_mul_left ha_pos
    exact hcross
  exact hij (totientAffine_parameters_injective e (Prod.ext haslope hresidue))

/-- The prescribed residue class for an evaluation input.  The zero channel
uses `3 mod 2^(e+3)` so that a prime value has totient exactly `2 mod 4`;
every positive-slope odd channel uses `1`. -/
def totientAffineBaseResidue {e : ℕ} : TotientAffineIndex e → ℕ
  | none => 3
  | some _ => 1

theorem totientAffineBaseResidue_odd {e : ℕ} (i : TotientAffineIndex e) :
    Odd (totientAffineBaseResidue i) := by
  cases i with
  | none => exact ⟨1, by norm_num [totientAffineBaseResidue]⟩
  | some i => exact ⟨0, by simp [totientAffineBaseResidue]⟩

/-- The fixed low two-adic part of the target prime minus one. -/
def totientAffineCore {e : ℕ} (i : TotientAffineIndex e) : ℕ :=
  totientAffineSlope i * totientAffineBaseResidue i +
    totientAffineResidue i - 1

theorem totientAffineBaseResidue_lt_modulus {e : ℕ} (i : TotientAffineIndex e) :
    totientAffineBaseResidue i < 2 ^ (e + 3) := by
  have hpow : 2 ^ 3 ≤ 2 ^ (e + 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  cases i <;> simp only [totientAffineBaseResidue] <;> norm_num at hpow ⊢ <;> omega

theorem totientAffineCore_pos {e : ℕ} (i : TotientAffineIndex e) :
    0 < totientAffineCore i := by
  cases i with
  | none => norm_num [totientAffineCore, totientAffineSlope,
      totientAffineBaseResidue, totientAffineResidue]
  | some i =>
      rcases i with ⟨j, r⟩
      simp only [totientAffineCore, totientAffineSlope, totientAffineBaseResidue,
        totientAffineResidue]
      have hpow : 0 < 2 ^ (j.val + 1) := by positivity
      omega



theorem totientAffineCore_lt_depthBound {e : ℕ} (i : TotientAffineIndex e) :
    totientAffineCore i < 2 ^ (e + 2) := by
  cases i with
  | none =>
      simp only [totientAffineCore, totientAffineSlope, totientAffineBaseResidue,
        totientAffineResidue]
      have : 4 ≤ 2 ^ (e + 2) := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  | some i =>
      rcases i with ⟨j, r⟩
      simp only [totientAffineCore, totientAffineSlope, totientAffineBaseResidue,
        totientAffineResidue]
      have hj : j.val + 1 ≤ e := by omega
      have hpow : 2 ^ (j.val + 1) ≤ 2 ^ e :=
        Nat.pow_le_pow_right (by omega) hj
      have hr := r.isLt
      have hfirst :
          2 ^ (j.val + 1) + (2 * r.val + 1) - 1 <
            2 * 2 ^ (j.val + 1) := by omega
      have hsecond : 2 * 2 ^ (j.val + 1) ≤ 2 * 2 ^ e :=
        Nat.mul_le_mul_left 2 hpow
      have hthird : 2 * 2 ^ e < 4 * 2 ^ e := by
        have hp : 0 < 2 ^ e := by positivity
        nlinarith
      simp only [mul_one]
      calc
        2 ^ (j.val + 1) + (2 * r.val + 1) - 1 < 2 * 2 ^ (j.val + 1) := hfirst
        _ ≤ 2 * 2 ^ e := hsecond
        _ < 4 * 2 ^ e := hthird
        _ = 2 ^ (e + 2) := by rw [pow_add]; ring

/-- Exact two-adic depth of the target core, bounded strictly below the depth
forced on every off-target column. -/
theorem exists_totientAffineCore_depth {e : ℕ} (i : TotientAffineIndex e) :
    ∃ d u : ℕ,
      d < e + 2 ∧ Odd u ∧ totientAffineCore i = 2 ^ d * u := by
  obtain ⟨d, u, hu, hcore⟩ :=
    Nat.exists_eq_two_pow_mul_odd (totientAffineCore_pos i).ne'
  refine ⟨d, u, ?_, hu, hcore⟩
  by_contra hd
  have hde : e + 2 ≤ d := by omega
  have hu_pos : 0 < u := hu.pos
  have hpow_le_core : 2 ^ d ≤ totientAffineCore i := by
    rw [hcore]
    exact Nat.le_mul_of_pos_right _ hu_pos
  have hbound : 2 ^ (e + 2) ≤ 2 ^ d :=
    Nat.pow_le_pow_right (by omega) hde
  exact (not_lt_of_ge (hbound.trans hpow_le_core))
    (totientAffineCore_lt_depthBound i)

/-- Uniformly choose distinct fresh primes in the class `1 mod 2^K` for a
finite collection of off-target channels. -/
theorem exists_large_distinct_primes_modEq_one
    {ι : Type*} [Fintype ι] (K B : ℕ) :
    ∃ q : ι → ℕ, Function.Injective q ∧
      ∀ i, (q i).Prime ∧ q i ≡ 1 [MOD 2 ^ K] ∧ B < q i := by
  classical
  let S : Set ℕ :=
    {p : ℕ | p.Prime ∧ p ≡ 1 [MOD 2 ^ K]} \ Set.Iic B
  have hpow : 2 ^ K ≠ 0 := by positivity
  have hS : S.Infinite := by
    exact (Nat.infinite_setOf_prime_modEq_one hpow).diff (Set.finite_Iic B)
  let emb : ℕ ↪ S := hS.natEmbedding S
  let enum : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let q : ι → ℕ := fun i => (emb (enum i).val).val
  refine ⟨q, ?_, ?_⟩
  · intro i j hij
    have hemb : emb (enum i).val = emb (enum j).val := Subtype.ext hij
    have hval : (enum i).val = (enum j).val := emb.injective hemb
    exact enum.injective (Fin.ext hval)
  · intro i
    have hi := (emb (enum i).val).property
    exact ⟨hi.1.1, hi.1.2, by simpa only [Set.mem_Iic, not_le] using hi.2⟩

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

/-- A CRT--Dirichlet row: the target affine value is prime, while every other
affine value has a distinct prime divisor congruent to one modulo the common
dyadic modulus. -/
structure TotientAffinePrimeRow (e : ℕ) (i : TotientAffineIndex e) where
  n : ℕ
  targetPrime : (totientAffineValue i n).Prime
  inputModEq : n ≡ totientAffineBaseResidue i [MOD 2 ^ (e + 3)]
  offPrime : ∀ j : TotientAffineIndex e, j ≠ i → ℕ
  offPrime_prime : ∀ (j : TotientAffineIndex e) (hji : j ≠ i),
    (offPrime j hji).Prime
  offPrime_modEq : ∀ (j : TotientAffineIndex e) (hji : j ≠ i),
    offPrime j hji ≡ 1 [MOD 2 ^ (e + 3)]
  offPrime_dvd : ∀ (j : TotientAffineIndex e) (hji : j ≠ i),
    offPrime j hji ∣ totientAffineValue j n

set_option maxHeartbeats 1000000 in
/-- CRT plus Dirichlet constructs a prime row for every target channel.  Only
one value is required to be prime; the off-target values merely receive fresh
prime divisors. -/
theorem exists_totientAffinePrimeRow (e : ℕ) (i : TotientAffineIndex e) :
    Nonempty (TotientAffinePrimeRow e i) := by
  classical
  let κ := {j : TotientAffineIndex e // j ≠ i}
  let T := 2 ^ (e + 3)
  let A := Finset.univ.sup (fun j : TotientAffineIndex e => totientAffineSlope j)
  let R := Finset.univ.sup (fun j : TotientAffineIndex e => totientAffineResidue j)
  let B := T + (A + 1) * (R + 1)
  have hT_pos : 0 < T := by simp [T]
  have hA (j : TotientAffineIndex e) : totientAffineSlope j ≤ A := by
    exact Finset.le_sup (f := fun j : TotientAffineIndex e => totientAffineSlope j)
      (Finset.mem_univ j)
  have hR (j : TotientAffineIndex e) : totientAffineResidue j ≤ R := by
    exact Finset.le_sup (f := fun j : TotientAffineIndex e => totientAffineResidue j)
      (Finset.mem_univ j)
  have hA_lt_B (j : TotientAffineIndex e) : totientAffineSlope j < B := by
    have hprod : A < (A + 1) * (R + 1) := by
      exact (Nat.lt_succ_self A).trans_le
        (Nat.le_mul_of_pos_right (A + 1) (Nat.succ_pos R))
    exact (hA j).trans_lt (hprod.trans_le (Nat.le_add_left _ _))
  have hT_lt_B : T < B := by
    dsimp only [B]
    have : 0 < (A + 1) * (R + 1) := by positivity
    omega
  have hcross_lt_B (j k : TotientAffineIndex e) :
      totientAffineSlope j * totientAffineResidue k < B := by
    have hmul : totientAffineSlope j * totientAffineResidue k ≤ A * R :=
      Nat.mul_le_mul (hA j) (hR k)
    have hstrict : A * R < (A + 1) * (R + 1) := by nlinarith
    exact hmul.trans_lt (hstrict.trans_le (Nat.le_add_left _ _))
  obtain ⟨q, hq_inj, hq⟩ :=
    exists_large_distinct_primes_modEq_one (ι := κ) (e + 3) B
  have hroot_exists (j : κ) :
      ∃ x < q j,
        q j ∣ totientAffineSlope j.val * x + totientAffineResidue j.val := by
    exact exists_affine_root_mod_prime (totientAffineSlope_pos j.val)
      ((hA_lt_B j.val).trans (hq j).2.2) (hq j).1
  let root : κ → ℕ := fun j => Classical.choose (hroot_exists j)
  have hroot_lt (j : κ) : root j < q j :=
    (Classical.choose_spec (hroot_exists j)).1
  have hroot_dvd (j : κ) :
      q j ∣ totientAffineSlope j.val * root j + totientAffineResidue j.val :=
    (Classical.choose_spec (hroot_exists j)).2
  let modulus : Option κ → ℕ
    | none => T
    | some j => q j
  let residue : Option κ → ℕ
    | none => totientAffineBaseResidue i
    | some j => root j
  have hmodulus_ne (x : Option κ) : modulus x ≠ 0 := by
    cases x with
    | none => exact hT_pos.ne'
    | some j => exact (hq j).1.ne_zero
  have hmodulus_pairwise :
      Set.Pairwise (↑(Finset.univ : Finset (Option κ)) : Set (Option κ))
        (Function.onFun Nat.Coprime modulus) := by
    intro x _ y _ hxy
    cases x with
    | none =>
        cases y with
        | none => exact (hxy rfl).elim
        | some j =>
            have hnot : ¬q j ∣ T :=
              Nat.not_dvd_of_pos_of_lt hT_pos (hT_lt_B.trans (hq j).2.2)
            exact ((hq j).1.coprime_iff_not_dvd.mpr hnot).symm
    | some j =>
        cases y with
        | none =>
            have hnot : ¬q j ∣ T :=
              Nat.not_dvd_of_pos_of_lt hT_pos (hT_lt_B.trans (hq j).2.2)
            exact (hq j).1.coprime_iff_not_dvd.mpr hnot
        | some k =>
            have hjk : j ≠ k := by
              intro hjk
              apply hxy
              simp [hjk]
            have hqne : q j ≠ q k := fun h => hjk (hq_inj h)
            apply ((hq j).1.coprime_iff_not_dvd).2
            intro hdvd
            have heq : q k = q j :=
              (((hq k).1.dvd_iff_eq (hq j).1.ne_one).mp hdvd)
            exact hqne heq.symm
  let crt := Nat.chineseRemainderOfFinset residue modulus Finset.univ
    (fun x _ => hmodulus_ne x) hmodulus_pairwise
  let Q := ∏ x : Option κ, modulus x
  have hcrt (x : Option κ) : crt.val ≡ residue x [MOD modulus x] :=
    crt.property x (Finset.mem_univ x)
  have hcrt_lt : crt.val < Q := by
    exact Nat.chineseRemainderOfFinset_lt_prod residue modulus
      (fun x _ => hmodulus_ne x) hmodulus_pairwise
  have hQ_ne : Q ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun x _ => hmodulus_ne x
  have hmodulus_dvd_Q (x : Option κ) : modulus x ∣ Q := by
    exact Finset.dvd_prod_of_mem modulus (Finset.mem_univ x)
  let targetStep := totientAffineSlope i * Q
  let targetBase := totientAffineValue i crt.val
  have htargetBase_lt : targetBase < targetStep := by
    have hsucc : crt.val + 1 ≤ Q := Nat.succ_le_iff.mpr hcrt_lt
    have hr := totientAffineResidue_lt_slope i
    dsimp only [targetBase, targetStep, totientAffineValue]
    calc
      totientAffineSlope i * crt.val + totientAffineResidue i <
          totientAffineSlope i * crt.val + totientAffineSlope i :=
        Nat.add_lt_add_left hr _
      _ = totientAffineSlope i * (crt.val + 1) := by ring
      _ ≤ totientAffineSlope i * Q := Nat.mul_le_mul_left _ hsucc
  have htargetBase_odd : Odd targetBase := by
    cases i with
    | none =>
        have hmod := hcrt (none : Option κ)
        simp only [modulus, residue, T, totientAffineBaseResidue] at hmod
        have hmod4 : crt.val ≡ 3 [MOD 4] :=
          hmod.of_dvd (by
            rw [show e + 3 = 2 + (e + 1) by omega, pow_add]
            exact dvd_mul_right _ _)
        have hodd : Odd crt.val := by
          rw [Nat.odd_iff]
          simpa [Nat.ModEq] using hmod4.of_dvd (by norm_num : 2 ∣ 4)
        simpa [targetBase, totientAffineValue, totientAffineSlope,
          totientAffineResidue] using hodd
    | some j =>
        rcases j with ⟨j, r⟩
        simp only [targetBase, totientAffineValue, totientAffineSlope,
          totientAffineResidue]
        have hevenSlope : Even (2 ^ (j.val + 1)) := by
          simpa [pow_succ, mul_comm] using Even.two_mul (2 ^ j.val)
        exact (hevenSlope.mul_right crt.val).add_odd (by simp)
  have htarget_coprime_slope : targetBase.Coprime (totientAffineSlope i) := by
    dsimp only [targetBase, totientAffineValue]
    rw [add_comm, Nat.coprime_add_mul_left_left]
    exact (totientAffineSlope_coprime_residue i).symm
  have htarget_coprime_Q : targetBase.Coprime Q := by
    rw [Nat.coprime_prod_right_iff]
    intro x _
    cases x with
    | none =>
        dsimp only [modulus, T]
        exact htargetBase_odd.coprime_two_right.pow_right (e + 3)
    | some j =>
        have hoffDvd : q j ∣ totientAffineValue j.val crt.val := by
          have hm := hcrt (some j)
          simp only [modulus, residue] at hm
          have hrootmod :
              totientAffineValue j.val crt.val ≡
                totientAffineValue j.val (root j) [MOD q j] := by
            exact (hm.mul_left (totientAffineSlope j.val)).add_right
              (totientAffineResidue j.val)
          exact Nat.modEq_zero_iff_dvd.mp
            (hrootmod.trans (Nat.modEq_zero_iff_dvd.mpr (hroot_dvd j)))
        exact affine_target_coprime_of_cross (hq j).1
          (totientAffine_cross_ne (fun h => j.property h.symm))
          ((hcross_lt_B j.val i).trans (hq j).2.2)
          ((hcross_lt_B i j.val).trans (hq j).2.2) hoffDvd
  have htargetCoprime : targetBase.Coprime targetStep := by
    exact htarget_coprime_slope.mul_right htarget_coprime_Q
  obtain ⟨p, hp_gt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq targetStep
      (mul_ne_zero (totientAffineSlope_pos i).ne' hQ_ne) htargetCoprime
  have hbase_le_p : targetBase ≤ p :=
    htargetBase_lt.le.trans hp_gt.le
  have hstep_dvd : targetStep ∣ p - targetBase :=
    (Nat.modEq_iff_dvd' hbase_le_p).mp hpmod.symm
  obtain ⟨t, ht⟩ := hstep_dvd
  have hp_eq : p = targetBase + targetStep * t := by omega
  let n := crt.val + Q * t
  have htargetValue : totientAffineValue i n = p := by
    dsimp only [n, targetBase, targetStep, totientAffineValue]
    rw [hp_eq]
    dsimp only [targetBase, targetStep, totientAffineValue]
    ring
  have hnMod : n ≡ totientAffineBaseResidue i [MOD 2 ^ (e + 3)] := by
    have hbase := hcrt (none : Option κ)
    have hTdQ : T ∣ Q := hmodulus_dvd_Q none
    have hQzero : Q * t ≡ 0 [MOD T] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hTdQ t)
    simpa [n, modulus, residue, T] using hbase.add hQzero
  let offPrime : ∀ j : TotientAffineIndex e, j ≠ i → ℕ := fun j hji =>
    q ⟨j, hji⟩
  refine ⟨⟨n, htargetValue.symm ▸ hp, hnMod, offPrime, ?_, ?_, ?_⟩⟩
  · intro j hji
    exact (hq ⟨j, hji⟩).1
  · intro j hji
    exact (hq ⟨j, hji⟩).2.1
  · intro j hji
    let k : κ := ⟨j, hji⟩
    have hbaseDvd : q k ∣ totientAffineValue j crt.val := by
      have hm := hcrt (some k)
      simp only [modulus, residue] at hm
      have hrootmod :
          totientAffineValue j crt.val ≡ totientAffineValue j (root k) [MOD q k] :=
        (hm.mul_left (totientAffineSlope j)).add_right (totientAffineResidue j)
      exact Nat.modEq_zero_iff_dvd.mp
        (hrootmod.trans (Nat.modEq_zero_iff_dvd.mpr (hroot_dvd k)))
    have hqdQ : q k ∣ Q := hmodulus_dvd_Q (some k)
    dsimp only [offPrime, n]
    dsimp only [k] at hbaseDvd hqdQ ⊢
    rw [show totientAffineValue j (crt.val + Q * t) =
        totientAffineValue j crt.val + totientAffineSlope j * Q * t by
          simp only [totientAffineValue]
          ring]
    exact dvd_add hbaseDvd (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right hqdQ (totientAffineSlope j)) t)

/-- The parity data extracted from a prime row. -/
structure TotientAffineParityRow (e : ℕ) (i : TotientAffineIndex e) where
  n : ℕ
  n_odd : Odd n
  depth : ℕ
  depth_lt : depth < e + 2
  target_dvd : 2 ^ depth ∣ Nat.totient (totientAffineValue i n)
  target_odd : Odd (Nat.totient (totientAffineValue i n) / 2 ^ depth)
  off_high : ∀ j : TotientAffineIndex e, j ≠ i →
    2 ^ (e + 2) ∣ Nat.totient (totientAffineValue j n)

/-- A prime row gives one low-depth diagonal entry and uniformly high-depth
off-diagonal entries. -/
theorem exists_totientAffineParityRow (e : ℕ) (i : TotientAffineIndex e) :
    Nonempty (TotientAffineParityRow e i) := by
  classical
  let row := Classical.choice (exists_totientAffinePrimeRow e i)
  obtain ⟨d, u, hd, hu, hcore⟩ := exists_totientAffineCore_depth i
  have hbase_le : totientAffineBaseResidue i ≤ row.n := by
    by_contra hnot
    have hnlt : row.n < totientAffineBaseResidue i := by omega
    have hne := row.inputModEq.eq_of_lt_of_lt
      (hnlt.trans (totientAffineBaseResidue_lt_modulus i))
      (totientAffineBaseResidue_lt_modulus i)
    omega
  have hT_dvd : 2 ^ (e + 3) ∣ row.n - totientAffineBaseResidue i :=
    (Nat.modEq_iff_dvd' hbase_le).mp row.inputModEq.symm
  obtain ⟨s, hs⟩ := hT_dvd
  have hn_eq : row.n = totientAffineBaseResidue i + 2 ^ (e + 3) * s := by
    omega
  have hone :
      1 ≤ totientAffineSlope i * totientAffineBaseResidue i +
        totientAffineResidue i := by
    have := totientAffineCore_pos i
    simp only [totientAffineCore] at this
    omega
  have hcore_succ :
      totientAffineCore i + 1 =
        totientAffineSlope i * totientAffineBaseResidue i +
          totientAffineResidue i := by
    exact Nat.sub_add_cancel hone
  have hminus :
      totientAffineValue i row.n - 1 =
        totientAffineCore i +
          totientAffineSlope i * 2 ^ (e + 3) * s := by
    have hvalue :
        totientAffineValue i row.n =
          (totientAffineSlope i * totientAffineBaseResidue i +
            totientAffineResidue i) +
            totientAffineSlope i * 2 ^ (e + 3) * s := by
      rw [hn_eq]
      simp only [totientAffineValue]
      ring
    rw [hvalue, ← hcore_succ]
    omega
  have hpowDvd : 2 ^ (d + 1) ∣ 2 ^ (e + 3) :=
    pow_dvd_pow 2 (by omega)
  obtain ⟨z, hz⟩ := hpowDvd
  let w := u + 2 * (totientAffineSlope i * z * s)
  have hfactor : totientAffineValue i row.n - 1 = 2 ^ d * w := by
    rw [hminus, hcore, hz]
    dsimp only [w]
    rw [pow_succ]
    ring
  have hwOdd : Odd w := by
    exact hu.add_even (by simp [w])
  have htargetTotient :
      Nat.totient (totientAffineValue i row.n) = 2 ^ d * w := by
    rw [Nat.totient_prime row.targetPrime, hfactor]
  have hnOdd : Odd row.n := by
    have htwoDvd : 2 ∣ 2 ^ (e + 3) := by
      change 2 ^ 1 ∣ 2 ^ (e + 3)
      exact pow_dvd_pow 2 (by omega)
    have hmod2 : row.n ≡ totientAffineBaseResidue i [MOD 2] :=
      row.inputModEq.of_dvd htwoDvd
    have hbaseOdd := totientAffineBaseResidue_odd i
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hn0 : row.n ≡ 0 [MOD 2] :=
      Nat.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp heven)
    exact (Nat.not_even_iff_odd.mpr hbaseOdd)
      (even_iff_two_dvd.mpr
        (Nat.modEq_zero_iff_dvd.mp (hmod2.symm.trans hn0)))
  refine ⟨⟨row.n, hnOdd, d, hd, ?_, ?_, ?_⟩⟩
  · exact ⟨w, htargetTotient⟩
  · rw [htargetTotient]
    simpa using hwOdd
  · intro j hji
    let q := row.offPrime j hji
    have hqPrime : q.Prime := row.offPrime_prime j hji
    have hqDvd : q ∣ totientAffineValue j row.n := row.offPrime_dvd j hji
    have hone_le_q : 1 ≤ q := hqPrime.one_le
    have hTq : 2 ^ (e + 3) ∣ q - 1 :=
      (Nat.modEq_iff_dvd' hone_le_q).mp (row.offPrime_modEq j hji).symm
    have hsmallT : 2 ^ (e + 2) ∣ 2 ^ (e + 3) := pow_dvd_pow 2 (by omega)
    exact hsmallT.trans (hTq.trans (by
      rw [← Nat.totient_prime hqPrime]
      exact Nat.totient_dvd_of_dvd hqDvd))

/-! ## A parity-separated determinant kernel -/

/-- A square natural matrix whose columns admit fixed powers of two and whose
quotient is the identity modulo two has nonzero determinant over `ℚ`.

This is the finite linear-algebra consumer for the CRT--Dirichlet rows below:
the target entry in column `j` has exact two-adic depth `depth j`, while every
off-target entry has at least one additional factor of two. -/
theorem paritySeparatedMatrix_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℕ) (depth : ι → ℕ)
    (hdiv : ∀ i j, 2 ^ depth j ∣ M i j)
    (hdiag : ∀ i, Odd (M i i / 2 ^ depth i))
    (hoff : ∀ i j, i ≠ j → Even (M i j / 2 ^ depth j)) :
    Matrix.det (fun i j => (M i j : ℚ)) ≠ 0 := by
  let B : Matrix ι ι ℤ := fun i j => (M i j / 2 ^ depth j : ℕ)
  have hBmod :
      (Int.castRingHom (ZMod 2)).mapMatrix B = (1 : Matrix ι ι (ZMod 2)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rcases hdiag i with ⟨k, hk⟩
      simp only [B, Matrix.one_apply, if_pos]
      change ((M i i / 2 ^ depth i : ℕ) : ZMod 2) = 1
      rw [hk]
      have htwo : (2 : ZMod 2) = 0 := by decide
      simp [htwo]
    · rcases hoff i j hij with ⟨k, hk⟩
      simp only [B, Matrix.one_apply, if_neg hij]
      change ((M i j / 2 ^ depth j : ℕ) : ZMod 2) = 0
      rw [hk]
      have htwo : (2 : ZMod 2) = 0 := by decide
      rw [Nat.cast_add]
      change (k : ZMod 2) + k = 0
      calc
        (k : ZMod 2) + k = (2 : ZMod 2) * k := by ring
        _ = 0 := by rw [htwo, zero_mul]
  have hdetB : Matrix.det B ≠ 0 := by
    intro hzero
    have hmap := (Int.castRingHom (ZMod 2)).map_det B
    rw [hBmod, Matrix.det_one, hzero, map_zero] at hmap
    exact zero_ne_one hmap
  let D : Matrix ι ι ℤ := Matrix.diagonal fun j => (2 ^ depth j : ℕ)
  have hfactor :
      (fun i j => (M i j : ℤ)) = B * D := by
    ext i j
    simp only [Matrix.mul_apply, D, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, B]
    exact_mod_cast (Nat.div_mul_cancel (hdiv i j)).symm
  have hdetD : Matrix.det D ≠ 0 := by
    simp only [D, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  have hdetInt : Matrix.det (fun i j => (M i j : ℤ)) ≠ 0 := by
    rw [hfactor, Matrix.det_mul]
    exact mul_ne_zero hdetB hdetD
  intro hzero
  have hmap := (Int.castRingHom ℚ).map_det (fun i j => (M i j : ℤ))
  have hmatrix :
      (Int.castRingHom ℚ).mapMatrix (fun i j => (M i j : ℤ)) =
        (fun i j => (M i j : ℚ)) := by
    ext i j
    simp
  rw [hmatrix, hzero] at hmap
  exact hdetInt (Int.cast_eq_zero.mp hmap)

/-- The CRT--Dirichlet rows assemble into a nonzero evaluation minor for the
normalized family on odd inputs. -/
theorem exists_separatedMinorCertificate_totientAffineOddFamily (e : ℕ) :
    Nonempty (SeparatedMinorCertificate (totientAffineOddFamily e)) := by
  classical
  let row : ∀ i : TotientAffineIndex e, TotientAffineParityRow e i := fun i =>
    Classical.choice (exists_totientAffineParityRow e i)
  let M : Matrix (TotientAffineIndex e) (TotientAffineIndex e) ℕ := fun i j =>
    Nat.totient (totientAffineValue j (row i).n)
  let depth : TotientAffineIndex e → ℕ := fun j => (row j).depth
  have hrowValue (i j : TotientAffineIndex e) :
      totientAffineOddFamily e j ((row i).n / 2) = (M i j : ℚ) := by
    simp only [totientAffineOddFamily, M]
    rw [Nat.two_mul_div_two_add_one_of_odd (row i).n_odd]
  refine ⟨⟨fun i => (row i).n / 2, ?_⟩⟩
  have hdet : Matrix.det (fun i j => (M i j : ℚ)) ≠ 0 := by
    apply paritySeparatedMatrix_det_ne_zero M depth
    · intro i j
      by_cases hij : i = j
      · subst j
        exact (row i).target_dvd
      · have hpow : 2 ^ depth j ∣ 2 ^ (e + 2) :=
          pow_dvd_pow 2 (row j).depth_lt.le
        exact hpow.trans ((row i).off_high j (fun h => hij h.symm))
    · intro i
      exact (row i).target_odd
    · intro i j hij
      have hdj : (row j).depth < e + 2 := (row j).depth_lt
      have hpow : 2 ^ ((row j).depth + 1) ∣ 2 ^ (e + 2) :=
        pow_dvd_pow 2 (by omega)
      obtain ⟨k, hk⟩ := hpow.trans
        ((row i).off_high j (fun h => hij h.symm))
      change Even (Nat.totient (totientAffineValue j (row i).n) / 2 ^ (row j).depth)
      refine ⟨k, ?_⟩
      rw [hk, pow_succ]
      simp [mul_assoc]
      omega
  have hmatrix :
      (fun i j => totientAffineOddFamily e j ((row i).n / 2)) =
        (fun i j => (M i j : ℚ)) := by
    funext i j
    exact hrowValue i j
  rw [hmatrix]
  exact hdet

/-- Unconditional linear independence of the normalized odd-input totient
channels at every finite dyadic level. -/
theorem linearIndependent_totientAffineOddFamily (e : ℕ) :
    LinearIndependent ℚ (totientAffineOddFamily e) := by
  exact linearIndependent_of_separatedMinorCertificate _
    (Classical.choice (exists_separatedMinorCertificate_totientAffineOddFamily e))

/-- The full canonical family is linearly independent.  Odd inputs first
separate the combined pair `φ(n), φ(2n)` from every odd residue channel; the
single even input `n = 2` then separates those two remaining columns. -/
theorem linearIndependent_canonicalTotientKernelFamily (e : ℕ) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hrel
  let c : TotientAffineIndex e → ℚ
    | none => g (Sum.inl 0) + g (Sum.inl 1)
    | some j => g (Sum.inr j)
  have hcRel : ∑ i, c i • totientAffineOddFamily e i = 0 := by
    funext m
    have hm := congrFun hrel (2 * m + 1)
    have hodd : Odd (2 * m + 1) := by simp
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hm
    change (∑ i, c i * totientAffineOddFamily e i m) = 0
    change (∑ i, g i * canonicalTotientKernelFamily e i (2 * m + 1)) = 0 at hm
    simp only [Fintype.sum_sum_type, Fintype.sum_option, Fin.sum_univ_two,
      canonicalTotientKernelFamily,
      totientKernelSeq, totientAffineOddFamily, totientAffineValue,
      totientAffineSlope, totientAffineResidue, c, one_mul, zero_add, pow_zero,
      pow_one, add_zero] at hm ⊢
    norm_num at hm
    rw [Nat.totient_two_mul_of_odd hodd] at hm
    linarith
  have hcZero : ∀ i, c i = 0 :=
    (Fintype.linearIndependent_iff.mp
      (linearIndependent_totientAffineOddFamily e)) c hcRel
  have hpair : g (Sum.inl 0) + g (Sum.inl 1) = 0 := by
    simpa only [c] using hcZero none
  have hinr : ∀ j, g (Sum.inr j) = 0 := by
    intro j
    simpa only [c] using hcZero (some j)
  have heven := congrFun hrel 2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heven
  change (∑ i, g i * canonicalTotientKernelFamily e i 2) = 0 at heven
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, canonicalTotientKernelFamily,
    totientKernelSeq, pow_zero, pow_one, one_mul, add_zero, hinr, zero_mul,
    Finset.sum_const_zero, Nat.totient_two] at heven
  norm_num at heven
  have hphi4 : Nat.totient 4 = 2 := by
    convert Nat.totient_prime_pow_succ Nat.prime_two 1 using 1 <;> norm_num
  rw [hphi4] at heven
  norm_num at heven
  have hsecond : g (Sum.inl 1) = 0 := by linarith
  have hfirst : g (Sum.inl 0) = 0 := by linarith
  intro i
  cases i with
  | inl i =>
      fin_cases i
      · exact hfirst
      · exact hsecond
  | inr j => exact hinr j



/-! ## The exact rank of the complete finite truncation -/









/-! ## The full dyadic kernel is infinite-dimensional -/

/-- The full dyadic kernel index, with the canonical residue range
`0 ≤ r < 2^j` at every level `j`. -/
abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

/-- Every canonical dyadic section of Euler's totient. -/
def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val
















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

/-- Index of the odd-core dyadic channels: the two zero-residue base channels
`n ↦ φ(n)` and `n ↦ φ(2n)`, and one channel for each odd residue at each
level. -/
abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)

/-- The odd-core family of dyadic totient sections, at every level at once. -/
def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1)

/-- The level of an odd-core channel: `0` for the two base channels, and one
more than the index level for an odd-residue channel. -/
def oddCoreLevel : TotientOddCoreIndex → ℕ
  | Sum.inl _ => 0
  | Sum.inr ⟨j, _⟩ => j + 1

/-- The canonical level-`e` index embeds in the odd-core index. -/
def canonicalToOddCore (e : ℕ) : TotientCanonicalIndex e → TotientOddCoreIndex
  | Sum.inl i => Sum.inl i
  | Sum.inr ⟨j, r⟩ => Sum.inr ⟨j.val, r⟩

/-- Truncate an odd-core index to level `e`.  The value at an index above level
`e` is junk; every lemma below restricts to indices of level at most `e`. -/
def oddCoreToCanonical (e : ℕ) : TotientOddCoreIndex → TotientCanonicalIndex e
  | Sum.inl i => Sum.inl i
  | Sum.inr ⟨j, r⟩ => if h : j < e then Sum.inr ⟨⟨j, h⟩, r⟩ else Sum.inl 0

/-- The odd-core family restricts to the canonical family at every level. -/
theorem oddCoreTotientKernelFamily_canonicalToOddCore (e : ℕ)
    (i : TotientCanonicalIndex e) :
    oddCoreTotientKernelFamily (canonicalToOddCore e i) =
      canonicalTotientKernelFamily e i := by
  cases i with
  | inl i => rfl
  | inr i => rcases i with ⟨j, r⟩; rfl

/-- Truncation is a left inverse of the embedding below the truncation level. -/
theorem canonicalToOddCore_oddCoreToCanonical {e : ℕ} {x : TotientOddCoreIndex}
    (hx : oddCoreLevel x ≤ e) :
    canonicalToOddCore e (oddCoreToCanonical e x) = x := by
  cases x with
  | inl i => rfl
  | inr i =>
      rcases i with ⟨j, r⟩
      have hj : j < e := by
        simpa [oddCoreLevel] using hx
      simp [oddCoreToCanonical, canonicalToOddCore, hj]

/-- **The odd-core dyadic totient channels are linearly independent over `ℚ`.**

Linear independence has finite character: every finite subfamily sits inside the
canonical level-`e` family for `e` above the largest level occurring, and those
are independent by the CRT--Dirichlet minor above. -/
theorem linearIndependent_oddCoreTotientKernelFamily :
    LinearIndependent ℚ oddCoreTotientKernelFamily := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  set e := s.sup oddCoreLevel with he
  have hround : ∀ x : {y // y ∈ s},
      canonicalToOddCore e (oddCoreToCanonical e x.val) = x.val := fun x =>
    canonicalToOddCore_oddCoreToCanonical (Finset.le_sup x.property)
  have hcomp :
      oddCoreTotientKernelFamily ∘ (Subtype.val : {y // y ∈ s} → _) =
        canonicalTotientKernelFamily e ∘
          fun x : {y // y ∈ s} => oddCoreToCanonical e x.val := by
    funext x
    simp only [Function.comp_apply]
    rw [← oddCoreTotientKernelFamily_canonicalToOddCore e, hround x]
  rw [hcomp]
  refine (linearIndependent_canonicalTotientKernelFamily e).comp _ ?_
  intro a b hab
  have hval := congrArg (canonicalToOddCore e) hab
  rw [hround a, hround b] at hval
  exact Subtype.ext hval

/-- Each odd-core channel is itself a dyadic section. -/
theorem range_oddCoreTotientKernelFamily_subset_full :
    Set.range oddCoreTotientKernelFamily ⊆ Set.range fullTotientKernelFamily := by
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i => exact ⟨⟨i.val, ⟨0, by positivity⟩⟩, rfl⟩
  | inr i =>
      rcases i with ⟨j, r⟩
      refine ⟨⟨j + 1, ⟨2 * r.val + 1, ?_⟩⟩, rfl⟩
      have hr : r.val < 2 ^ j := r.isLt
      rw [pow_succ]
      omega

/-- The zero-residue channel at every level is a rational multiple of one of the
two base channels. -/
theorem totientKernelSeq_zero_mem_span_oddCore (j : ℕ) :
    totientKernelSeq j 0 ∈
      Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) := by
  cases j with
  | zero => exact Submodule.subset_span ⟨Sum.inl 0, rfl⟩
  | succ j =>
      have hbase : oddCoreTotientKernelFamily (Sum.inl 1) = totientKernelSeq 1 0 :=
        rfl
      have hfun :
          totientKernelSeq (j + 1) 0 = (2 ^ j : ℚ) • totientKernelSeq 1 0 := by
        funext n
        simpa using totientKernel_zero_residue j n
      rw [hfun, ← hbase]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl 1, rfl⟩)

/-- An odd residue below its level names an odd-core channel outright. -/
theorem totientKernelSeq_odd_mem_span_oddCore {j r : ℕ} (hodd : r % 2 = 1)
    (hlt : r < 2 ^ j) :
    totientKernelSeq j r ∈
      Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := by
    refine ⟨j - 1, ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp at hlt; omega
    · omega
  obtain ⟨r', rfl⟩ : ∃ r', r = 2 * r' + 1 := ⟨r / 2, by omega⟩
  have hr' : r' < 2 ^ j := by
    rw [pow_succ] at hlt
    omega
  exact Submodule.subset_span ⟨Sum.inr ⟨j, ⟨r', hr'⟩⟩, rfl⟩

/-- **Every canonical dyadic section of `φ` lies in the span of the odd-core
family.**  Zero residues reduce by `totientKernel_zero_residue`, even positive
residues by `totientKernel_even_residue_reduce` applied at the exact two-adic
valuation of the residue, and odd residues are already odd-core channels. -/
theorem totientKernelSeq_mem_span_oddCore (j r : ℕ) (hlt : r < 2 ^ j) :
    totientKernelSeq j r ∈
      Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) := by
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · exact totientKernelSeq_zero_mem_span_oddCore j
  by_cases hodd : r % 2 = 1
  · exact totientKernelSeq_odd_mem_span_oddCore hodd hlt
  obtain ⟨k, s, hs, hrks⟩ := Nat.exists_eq_two_pow_mul_odd (n := r) (by omega)
  have hsodd : s % 2 = 1 := Nat.odd_iff.mp hs
  have hspos : 0 < s := by omega
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hrks; omega
    · exact hk
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hpow_le : 2 ^ (t + 1) ≤ r := by
    rw [hrks]
    exact Nat.le_mul_of_pos_right _ hspos
  have hpow_lt : (2 : ℕ) ^ (t + 1) < 2 ^ j := lt_of_le_of_lt hpow_le hlt
  have htj : t + 1 < j := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpow_lt
  have hsplit : 2 ^ (t + 1) * 2 ^ (j - (t + 1)) = 2 ^ j := by
    rw [← pow_add]
    congr 1
    omega
  have hslt : s < 2 ^ (j - (t + 1)) := by
    have hmul : 2 ^ (t + 1) * s < 2 ^ (t + 1) * 2 ^ (j - (t + 1)) := by
      rw [hsplit, ← hrks]
      exact hlt
    exact lt_of_mul_lt_mul_left hmul (Nat.zero_le _)
  have hfun :
      totientKernelSeq j r =
        (2 ^ t : ℚ) • totientKernelSeq (j - (t + 1)) s := by
    funext n
    rw [hrks]
    simpa using totientKernel_even_residue_reduce j t s n htj hs
  rw [hfun]
  exact Submodule.smul_mem _ _
    (totientKernelSeq_odd_mem_span_oddCore hsodd hslt)

/-- **The odd-core family spans every dyadic section of `φ`.**  With
`linearIndependent_oddCoreTotientKernelFamily` this fixes the complete
`ℚ`-linear relation structure of the dyadic sections of Euler's totient. -/
theorem span_range_fullTotientKernel_eq_span_range_oddCore :
    Submodule.span ℚ (Set.range fullTotientKernelFamily) =
      Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) := by
  refine le_antisymm ?_
    (Submodule.span_mono range_oddCoreTotientKernelFamily_subset_full)
  rw [Submodule.span_le]
  rintro _ ⟨⟨j, r⟩, rfl⟩
  exact totientKernelSeq_mem_span_oddCore j r.val r.isLt

/-- **An explicit basis for the `ℚ`-span of all dyadic sections of Euler's
totient**, indexed by the two zero-residue base channels together with one
channel per odd residue per level. -/
noncomputable def totientDyadicSectionBasis :
    Basis TotientOddCoreIndex ℚ
      (Submodule.span ℚ (Set.range fullTotientKernelFamily)) :=
  (Basis.span linearIndependent_oddCoreTotientKernelFamily).map
    (LinearEquiv.ofEq _ _ span_range_fullTotientKernel_eq_span_range_oddCore.symm)


end Erdos249257


