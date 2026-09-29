-- Prove2me | Definitions.Def_Erdos249257_AllBaseTotientKernel_v2
-- name    : Erdos249257_AllBaseTotientKernel_v2
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T01:11:39.187913+00:00
-- url     : https://prove2.me/theorems/5d995917-95ae-40b3-b3be-5c32afae3435
-- title:
--   All-base totient families and affine separation
-- statement:
--   Defines finite all-base totient families and proves their linear independence by an explicit separated evaluation minor. The independence conclusion is already subsumed by Greg Martin’s earlier theorem; the formal proof is an independent finite-determinant route.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/AllBaseTotientKernel.lean#L867-L875
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/AllBaseTotientKernel.lean#L1093-L1125
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/AllBaseTotientKernel.lean#L1214-L1240
--   Pinned source origin note: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/AllBaseTotientKernel.lean#L18-L35
--   Prior mathematical result subsuming the independence conclusion: https://arxiv.org/abs/math/0603053

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect_v2
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# The all-base totient kernel: unconditional independence, exact rank, explicit basis

`TotientMahlerDefect.lean` proves the dyadic (`k = 2`) case unconditionally by a
*two-adic parity determinant*, and that argument is structurally restricted to
**odd slopes**: the separating prime is the fixed prime `2`, so a channel with an
even slope cannot be separated from the zero channel.  This module removes that
restriction by replacing the fixed prime `2` with an *auxiliary prime* `ℓ` chosen
after the family, and then uses the resulting diagonal-mod-`ℓ` determinant to get
the exact finite-level rank of the totient `k`-kernel for every integer base
`k ≥ 2`, together with an explicit `Basis`.

## Attribution

Greg Martin, *Simultaneous inequalities among values of the Euler φ-function*,
arXiv:math/0603053, Theorem 1, already gives a **positive lower density** of
integers at which prescribed simultaneous dominance among `φ(a_i n + b_i)` holds,
for arbitrary positive slopes `a_i` and non-proportional affine forms.  That
theorem is strictly stronger than, and subsumes, the linear-independence
conclusion proved here.

What is contributed in this file is therefore **not an original theorem**.  It is

* a Lean formalisation, by an *independent finite-determinant proof* (an explicit
  square evaluation minor that is diagonal modulo one auxiliary prime), and
* the removal of the odd-slope restriction that the two-adic parity argument in
  `TotientMahlerDefect.lean` requires.

The exact rank formula `dim_ℚ V_{k,e} = k^e + 1`, the explicit basis, and the
relation normal form have **no located source** and are novelty-unassessed; they
are stated and proved here as consequences of the independence theorem plus the
elementary reduction identities, not claimed as new mathematics.

The reduction identities restated in the "Reduction identities" section below were proved
in `formal_math/odd_slope_affine_totient/TotientKernelReduction.lean`, which is a
separate Lake project and cannot be imported from here; they are restated with
their proofs rather than re-derived differently.

## Main results

* `AllSlopeAffineFamily` — a finite family of affine forms `content i * (slope i * n + residue i)`
  with `slope i` coprime to `residue i` and pairwise nonzero cross-determinants.
  **No parity or odd-slope hypothesis.**
* `exists_auxiliaryPrimeSeparatedRow` — for each target index, a row on which the
  target totient value is prime to `ℓ` and every other totient value is divisible by `ℓ`.
* `AllSlopeAffineFamily.linearIndependent`, `linearIndependent_totientAffineForms` —
  unconditional `ℚ`-linear independence of `n ↦ φ(a i * n + b i)`.
* `linearIndependent_totientPowAffineForms` — the same conclusion for the
  extension class `n ↦ n^q φ(n)^m`, `m ≥ 1`, from the same rows.
* `finrank_allBaseTotientKernel_eq`, `finrank_allBaseThroughLevelFamily_eq` —
  the exact rank `k^e + 1`.
* `allBaseTotientKernelBasis` — an explicit `Basis` of the level-`e` kernel span.
* `allBaseZeroSyzygy_mem_ker`, `allBaseStepSyzygy_mem_ker`,
  `finrank_allBaseRelationModule_eq` — the named syzygies and the exact dimension
  `k + k² + ⋯ + k^{e−1}` of the relation module.

Nothing here proves an irrationality statement; it is a theorem about `φ`.
-/

namespace Erdos249257

open Module Matrix

/-! ## Dirichlet and CRT inputs at an arbitrary modulus

`TotientMahlerDefect.exists_large_distinct_primes_modEq_one` is specialised to the
modulus `2 ^ K`.  The all-base argument needs the same statement at an arbitrary
nonzero modulus, so it is restated here. -/

/-- Uniformly choose distinct fresh primes in the class `1 mod N`, for a finite
collection of off-target channels and an arbitrary nonzero modulus `N`. -/
theorem exists_large_distinct_primes_modEq_one_of_modulus
    {ι : Type*} [Fintype ι] {N : ℕ} (hN : N ≠ 0) (B : ℕ) :
    ∃ q : ι → ℕ, Function.Injective q ∧
      ∀ i, (q i).Prime ∧ q i ≡ 1 [MOD N] ∧ B < q i := by
  classical
  let S : Set ℕ := {p : ℕ | p.Prime ∧ p ≡ 1 [MOD N]} \ Set.Iic B
  have hS : S.Infinite :=
    (Nat.infinite_setOf_prime_modEq_one hN).diff (Set.finite_Iic B)
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

/-- A nonzero affine form hits every prescribed residue class modulo a prime that
exceeds its slope.  This is the inhomogeneous companion of
`exists_affine_root_mod_prime`, needed because the target row must land in the
class `2 mod ℓ` rather than in the class `0`. -/
theorem exists_affine_value_mod_prime {a b c q : ℕ}
    (ha : 0 < a) (haq : a < q) (hq : q.Prime) :
    ∃ x < q, a * x + b ≡ c [MOD q] := by
  have hnot : ¬q ∣ a := Nat.not_dvd_of_pos_of_lt ha haq
  have hac : a.Coprime q := (hq.coprime_iff_not_dvd.mpr hnot).symm
  obtain ⟨x, hxlt, hx⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (c + b * (q - 1)) hac hq.ne_zero
  refine ⟨x, hxlt, ?_⟩
  have hx' : a * x ≡ c + b * (q - 1) [MOD q] := hx
  have hstep : a * x + b ≡ c + b * (q - 1) + b [MOD q] := hx'.add_right b
  have hsum : c + b * (q - 1) + b = c + b * q := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq.one_lt; omega⟩
    simp only [Nat.add_sub_cancel, Nat.mul_succ]
    omega
  rw [hsum] at hstep
  refine hstep.trans ?_
  simp

/-! ## A determinant that is diagonal modulo one prime -/

/-- A natural number reduces to zero in `ZMod n` exactly when `n` divides it. -/
theorem natCast_zmod_eq_zero_iff_dvd' (a n : ℕ) : ((a : ℕ) : ZMod n) = 0 ↔ n ∣ a := by
  have h : ((a : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) ↔ a ≡ 0 [MOD n] :=
    ZMod.natCast_eq_natCast_iff a 0 n
  simpa using h.trans Nat.modEq_zero_iff_dvd

/-- A square natural matrix which is diagonal modulo a prime, with every diagonal
entry prime to that prime, has nonzero determinant over `ℚ`.

This is the all-base replacement for `paritySeparatedMatrix_det_ne_zero`: instead
of exact two-adic depths it uses a single auxiliary prime `ℓ`, which is what makes
the argument work for even slopes. -/
theorem det_ne_zero_of_diagonal_mod_prime
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (M : Matrix ι ι ℕ)
    (hoff : ∀ i j, i ≠ j → ℓ ∣ M i j)
    (hdiag : ∀ i, ¬ ℓ ∣ M i i) :
    Matrix.det (fun i j => (M i j : ℚ)) ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set N : Matrix ι ι ℤ := (fun i j => (M i j : ℤ)) with hNdef
  have hmapped :
      (Int.castRingHom (ZMod ℓ)).mapMatrix N =
        Matrix.diagonal (fun i => ((M i i : ℕ) : ZMod ℓ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hNdef, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      have hz : ((M i j : ℕ) : ZMod ℓ) = 0 :=
        (natCast_zmod_eq_zero_iff_dvd' _ _).mpr (hoff i j hij)
      simpa [hNdef] using hz
  have hdetZMod : Matrix.det ((Int.castRingHom (ZMod ℓ)).mapMatrix N) ≠ 0 := by
    rw [hmapped, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    intro hzero
    exact hdiag i ((natCast_zmod_eq_zero_iff_dvd' _ _).mp hzero)
  have hdetInt : Matrix.det N ≠ 0 := by
    intro hzero
    rw [← (Int.castRingHom (ZMod ℓ)).map_det N, hzero, map_zero] at hdetZMod
    exact hdetZMod rfl
  intro hzero
  have hmap := (Int.castRingHom ℚ).map_det N
  have hmatrix :
      (Int.castRingHom ℚ).mapMatrix N = (fun i j => (M i j : ℚ)) := by
    ext i j
    simp [hNdef]
  rw [hmatrix, hzero] at hmap
  exact hdetInt (Int.cast_eq_zero.mp hmap)

/-! ## The all-slope affine totient family

The generalisation of `totientAffineFamily`.  A channel is
`n ↦ φ (content i * (slope i * n + residue i))` with `slope i` coprime to
`residue i`; the pairwise condition is that the cross determinants
`slope i * residue j - slope j * residue i` are nonzero.  There is **no odd-slope
hypothesis**. -/





/-- A finite family of normalized positive affine forms with pairwise nonzero
cross determinants. -/
structure AllSlopeAffineFamily (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The content, i.e. the common factor `gcd (a i) (b i)` pulled out in front. -/
  content : ι → ℕ
  /-- The primitive slope `a i / gcd (a i) (b i)`. -/
  slope : ι → ℕ
  /-- The primitive residue `b i / gcd (a i) (b i)`. -/
  residue : ι → ℕ
  content_pos : ∀ i, 0 < content i
  slope_pos : ∀ i, 0 < slope i
  residue_pos : ∀ i, 0 < residue i
  coprime : ∀ i, Nat.Coprime (slope i) (residue i)
  cross_ne : ∀ i j, i ≠ j → slope i * residue j ≠ slope j * residue i

namespace AllSlopeAffineFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The natural-number value of channel `i` at `n`. -/
def value (F : AllSlopeAffineFamily ι) (i : ι) (n : ℕ) : ℕ :=
  F.content i * (F.slope i * n + F.residue i)

/-- The rational-valued totient channel of the family. -/
def family (F : AllSlopeAffineFamily ι) : ι → ℕ → ℚ := fun i n =>
  (Nat.totient (F.value i n) : ℚ)



/-- An auxiliary prime for the family: an odd prime exceeding every slope and
every content.  Such a prime exists because the index type is finite. -/
theorem exists_auxiliaryPrime (F : AllSlopeAffineFamily ι) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 2 < ℓ ∧ (∀ i, F.slope i < ℓ) ∧ (∀ i, F.content i < ℓ) := by
  classical
  obtain ⟨ℓ, hge, hp⟩ :=
    Nat.exists_infinite_primes
      (Finset.univ.sup F.slope + Finset.univ.sup F.content + 3)
  refine ⟨ℓ, hp, by omega, fun i => ?_, fun i => ?_⟩
  · have h1 : F.slope i ≤ Finset.univ.sup F.slope :=
      Finset.le_sup (f := F.slope) (Finset.mem_univ i)
    omega
  · have h2 : F.content i ≤ Finset.univ.sup F.content :=
      Finset.le_sup (f := F.content) (Finset.mem_univ i)
    omega

set_option maxHeartbeats 1000000 in
/-- **The auxiliary-prime separated row.**  Fix an odd prime `ℓ` exceeding every
slope and content of the family, and a target index `i`.  Then there is an
evaluation point `n` at which

* `φ (value i n)` is prime to `ℓ`, and
* `φ (value j n)` is divisible by `ℓ` for every other channel `j`.

The construction is CRT plus Dirichlet, exactly as in
`exists_totientAffinePrimeRow`, but with the fixed prime `2` replaced by `ℓ`:
each off-target channel is forced to acquire a fresh prime divisor `q` in the
class `1 mod ℓ`, so that `ℓ ∣ q - 1 ∣ φ (value j n)`, while the target channel is
made `content i` times a prime `p ≡ 2 (mod ℓ)`, so that
`φ (value i n) = φ (content i) * (p - 1) ≡ φ (content i) ≢ 0 (mod ℓ)`.

The row is returned together with the prime `p` and its class, because the same
row separates every weight `n ↦ n^q φ(n)^m` and not only `φ` itself. -/
theorem exists_auxiliaryPrimeSeparatedRow_data (F : AllSlopeAffineFamily ι)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : 2 < ℓ)
    (hslopelt : ∀ i, F.slope i < ℓ) (_hcontentlt : ∀ i, F.content i < ℓ)
    (i : ι) :
    ∃ n p : ℕ, p.Prime ∧ F.content i < p ∧ p ≡ 2 [MOD ℓ] ∧
      F.value i n = F.content i * p ∧
      ∀ j : ι, j ≠ i → ℓ ∣ Nat.totient (F.value j n) := by
  classical
  let κ := {j : ι // j ≠ i}
  let A := Finset.univ.sup F.slope
  let R := Finset.univ.sup F.residue
  let B := ℓ + (A + 1) * (R + 1)
  have hℓ_pos : 0 < ℓ := hℓ.pos
  have hA : ∀ j, F.slope j ≤ A := fun j =>
    Finset.le_sup (f := F.slope) (Finset.mem_univ j)
  have hR : ∀ j, F.residue j ≤ R := fun j =>
    Finset.le_sup (f := F.residue) (Finset.mem_univ j)
  have hA_lt_B : ∀ j, F.slope j < B := by
    intro j
    have hprod : A < (A + 1) * (R + 1) :=
      (Nat.lt_succ_self A).trans_le (Nat.le_mul_of_pos_right (A + 1) (Nat.succ_pos R))
    exact (hA j).trans_lt (hprod.trans_le (Nat.le_add_left _ _))
  have hℓ_lt_B : ℓ < B := by
    dsimp only [B]
    have : 0 < (A + 1) * (R + 1) := by positivity
    omega
  have hcross_lt_B : ∀ j k, F.slope j * F.residue k < B := by
    intro j k
    have hmul : F.slope j * F.residue k ≤ A * R := Nat.mul_le_mul (hA j) (hR k)
    have hstrict : A * R < (A + 1) * (R + 1) := by nlinarith
    exact hmul.trans_lt (hstrict.trans_le (Nat.le_add_left _ _))
  obtain ⟨q, hq_inj, hq⟩ :=
    exists_large_distinct_primes_modEq_one_of_modulus (ι := κ) hℓ_pos.ne' B
  -- roots for the off-target channels
  have hroot_exists : ∀ j : κ,
      ∃ x < q j, q j ∣ F.slope j.val * x + F.residue j.val := by
    intro j
    exact exists_affine_root_mod_prime (F.slope_pos j.val)
      ((hA_lt_B j.val).trans (hq j).2.2) (hq j).1
  let root : κ → ℕ := fun j => Classical.choose (hroot_exists j)
  have hroot_dvd : ∀ j : κ, q j ∣ F.slope j.val * root j + F.residue j.val :=
    fun j => (Classical.choose_spec (hroot_exists j)).2
  -- the target class `2 mod ℓ`
  obtain ⟨x₀, hx₀lt, hx₀⟩ :=
    exists_affine_value_mod_prime (a := F.slope i) (b := F.residue i) (c := 2)
      (F.slope_pos i) (hslopelt i) hℓ
  let modulus : Option κ → ℕ
    | none => ℓ
    | some j => q j
  let residue : Option κ → ℕ
    | none => x₀
    | some j => root j
  have hmodulus_ne : ∀ x : Option κ, modulus x ≠ 0 := by
    intro x
    cases x with
    | none => exact hℓ_pos.ne'
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
            have hnot : ¬q j ∣ ℓ :=
              Nat.not_dvd_of_pos_of_lt hℓ_pos (hℓ_lt_B.trans (hq j).2.2)
            exact ((hq j).1.coprime_iff_not_dvd.mpr hnot).symm
    | some j =>
        cases y with
        | none =>
            have hnot : ¬q j ∣ ℓ :=
              Nat.not_dvd_of_pos_of_lt hℓ_pos (hℓ_lt_B.trans (hq j).2.2)
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
  have hcrt : ∀ x : Option κ, crt.val ≡ residue x [MOD modulus x] :=
    fun x => crt.property x (Finset.mem_univ x)
  have hQ_ne : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => hmodulus_ne x
  have hmodulus_dvd_Q : ∀ x : Option κ, modulus x ∣ Q :=
    fun x => Finset.dvd_prod_of_mem modulus (Finset.mem_univ x)
  let targetBase := F.slope i * crt.val + F.residue i
  let targetStep := F.slope i * Q
  -- coprimality of the Dirichlet progression
  have htarget_coprime_slope : Nat.Coprime targetBase (F.slope i) := by
    dsimp only [targetBase]
    rw [add_comm, Nat.coprime_add_mul_left_left]
    exact (F.coprime i).symm
  have htargetBase_mod : targetBase ≡ 2 [MOD ℓ] := by
    have hbase := hcrt (none : Option κ)
    simp only [modulus, residue] at hbase
    have := (hbase.mul_left (F.slope i)).add_right (F.residue i)
    exact this.trans hx₀
  have hℓ_not_dvd_targetBase : ¬ ℓ ∣ targetBase := by
    intro hdvd
    have h0 : targetBase ≡ 0 [MOD ℓ] := (Nat.modEq_zero_iff_dvd).mpr hdvd
    have h2 : (2 : ℕ) ≡ 0 [MOD ℓ] := htargetBase_mod.symm.trans h0
    have : ℓ ∣ 2 := (Nat.modEq_zero_iff_dvd).mp h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have htarget_coprime_ℓ : Nat.Coprime targetBase ℓ :=
    (hℓ.coprime_iff_not_dvd.mpr hℓ_not_dvd_targetBase).symm
  have htarget_coprime_Q : Nat.Coprime targetBase Q := by
    rw [Nat.coprime_prod_right_iff]
    intro x _
    cases x with
    | none => exact htarget_coprime_ℓ
    | some j =>
        have hoffDvd : q j ∣ F.slope j.val * crt.val + F.residue j.val := by
          have hm := hcrt (some j)
          simp only [modulus, residue] at hm
          have hrootmod :
              F.slope j.val * crt.val + F.residue j.val ≡
                F.slope j.val * root j + F.residue j.val [MOD q j] :=
            (hm.mul_left (F.slope j.val)).add_right (F.residue j.val)
          exact Nat.modEq_zero_iff_dvd.mp
            (hrootmod.trans (Nat.modEq_zero_iff_dvd.mpr (hroot_dvd j)))
        exact affine_target_coprime_of_cross (hq j).1
          (F.cross_ne j.val i (j.property))
          ((hcross_lt_B j.val i).trans (hq j).2.2)
          ((hcross_lt_B i j.val).trans (hq j).2.2) hoffDvd
  have htargetCoprime : Nat.Coprime targetBase targetStep :=
    htarget_coprime_slope.mul_right htarget_coprime_Q
  obtain ⟨p, hp_gt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (targetBase + targetStep + F.content i)
      (mul_ne_zero (F.slope_pos i).ne' hQ_ne) htargetCoprime
  have hbase_le_p : targetBase ≤ p := by omega
  have hcontent_lt_p : F.content i < p := by omega
  obtain ⟨t, ht⟩ : targetStep ∣ p - targetBase :=
    (Nat.modEq_iff_dvd' hbase_le_p).mp hpmod.symm
  have hp_eq : p = targetBase + targetStep * t := by omega
  refine ⟨crt.val + Q * t, p, hp, hcontent_lt_p, ?_, ?_, ?_⟩
  · -- the target prime lies in the class `2 mod ℓ`
    have hℓQ : ℓ ∣ targetStep :=
      (hmodulus_dvd_Q (none : Option κ)).trans (Dvd.intro_left (F.slope i) rfl)
    have hstep0 : targetStep * t ≡ 0 [MOD ℓ] :=
      Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.mul_right hℓQ t)
    have hchain : p ≡ targetBase + 0 [MOD ℓ] := by
      rw [hp_eq]; exact (Nat.ModEq.refl targetBase).add hstep0
    simpa using hchain.trans htargetBase_mod
  · -- the target value is `content i * p`
    simp only [value, hp_eq]
    dsimp only [targetBase, targetStep]
    ring
  · -- every off-target value acquires the fresh prime `q j ≡ 1 (mod ℓ)`
    intro j hji
    let k : κ := ⟨j, hji⟩
    have hbaseDvd : q k ∣ F.slope j * crt.val + F.residue j := by
      have hm := hcrt (some k)
      simp only [modulus, residue] at hm
      have hrootmod :
          F.slope j * crt.val + F.residue j ≡
            F.slope j * root k + F.residue j [MOD q k] :=
        (hm.mul_left (F.slope j)).add_right (F.residue j)
      exact Nat.modEq_zero_iff_dvd.mp
        (hrootmod.trans (Nat.modEq_zero_iff_dvd.mpr (hroot_dvd k)))
    have hqdQ : q k ∣ Q := hmodulus_dvd_Q (some k)
    have hdvdValue : q k ∣ F.value j (crt.val + Q * t) := by
      have hsplit : F.slope j * (crt.val + Q * t) + F.residue j =
          (F.slope j * crt.val + F.residue j) + F.slope j * Q * t := by ring
      have : q k ∣ F.slope j * (crt.val + Q * t) + F.residue j := by
        rw [hsplit]
        exact dvd_add hbaseDvd
          (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqdQ (F.slope j)) t)
      exact Dvd.dvd.mul_left this (F.content j)
    have hqmod : q k ≡ 1 [MOD ℓ] := (hq k).2.1
    have hℓdvd : ℓ ∣ q k - 1 := (Nat.modEq_iff_dvd' (hq k).1.one_le).mp hqmod.symm
    have htotdvd : Nat.totient (q k) ∣ Nat.totient (F.value j (crt.val + Q * t)) :=
      Nat.totient_dvd_of_dvd hdvdValue
    rw [Nat.totient_prime (hq k).1] at htotdvd
    exact hℓdvd.trans htotdvd

theorem auxPrime_not_dvd_pred {ℓ p : ℕ} (hℓ2 : 2 < ℓ) (hge : 2 ≤ p)
    (hp2 : p ≡ 2 [MOD ℓ]) : ¬ ℓ ∣ (p - 1) := by
  have hdvd2 : ℓ ∣ p - 2 := (Nat.modEq_iff_dvd' hge).mp hp2.symm
  intro hdvd1
  have hone : ℓ ∣ 1 := by
    have := Nat.dvd_sub hdvd1 hdvd2
    simpa [show p - 1 - (p - 2) = 1 by omega] using this
  have := Nat.le_of_dvd (by norm_num) hone
  omega



theorem auxPrime_not_dvd_totient_content (F : AllSlopeAffineFamily ι) {ℓ : ℕ}
    (hcontentlt : ∀ i, F.content i < ℓ) (i : ι) :
    ¬ ℓ ∣ Nat.totient (F.content i) := by
  have hpos : 0 < Nat.totient (F.content i) := Nat.totient_pos.mpr (F.content_pos i)
  have hle : Nat.totient (F.content i) ≤ F.content i := Nat.totient_le _
  exact Nat.not_dvd_of_pos_of_lt hpos (by have := hcontentlt i; omega)

/-- **Auxiliary-prime separation for `φ`**: on the row supplied by
`exists_auxiliaryPrimeSeparatedRow_data` the target totient is prime to `ℓ` and
every other totient is divisible by `ℓ`. -/
theorem exists_auxiliaryPrimeSeparatedRow (F : AllSlopeAffineFamily ι)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : 2 < ℓ)
    (hslopelt : ∀ i, F.slope i < ℓ) (hcontentlt : ∀ i, F.content i < ℓ)
    (i : ι) :
    ∃ n : ℕ, ¬ (ℓ ∣ Nat.totient (F.value i n)) ∧
      ∀ j : ι, j ≠ i → ℓ ∣ Nat.totient (F.value j n) := by
  obtain ⟨n, p, hp, hcp, hp2, hval, hoff⟩ :=
    F.exists_auxiliaryPrimeSeparatedRow_data hℓ hℓ2 hslopelt hcontentlt i
  refine ⟨n, ?_, hoff⟩
  have hcop : Nat.Coprime (F.content i) p :=
    (hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (F.content_pos i) hcp)).symm
  have htot : Nat.totient (F.value i n) = Nat.totient (F.content i) * (p - 1) := by
    rw [hval, Nat.totient_mul hcop, Nat.totient_prime hp]
  rw [htot]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h | h
  · exact auxPrime_not_dvd_totient_content F hcontentlt i h
  · exact auxPrime_not_dvd_pred hℓ2 hp.two_le hp2 h

/-- **The all-slope separated minor.**  Assembling one auxiliary-prime row per
channel gives a square evaluation matrix which is diagonal modulo `ℓ` with
nonzero diagonal, hence has nonzero determinant. -/
theorem exists_separatedMinorCertificate (F : AllSlopeAffineFamily ι) :
    Nonempty (SeparatedMinorCertificate F.family) := by
  classical
  obtain ⟨ℓ, hℓ, hℓ2, hslopelt, hcontentlt⟩ := F.exists_auxiliaryPrime
  have hrow : ∀ i : ι, ∃ n : ℕ, ¬ (ℓ ∣ Nat.totient (F.value i n)) ∧
      ∀ j : ι, j ≠ i → ℓ ∣ Nat.totient (F.value j n) :=
    fun i => F.exists_auxiliaryPrimeSeparatedRow hℓ hℓ2 hslopelt hcontentlt i
  let point : ι → ℕ := fun i => Classical.choose (hrow i)
  have hpoint : ∀ i, ¬ (ℓ ∣ Nat.totient (F.value i (point i))) ∧
      ∀ j : ι, j ≠ i → ℓ ∣ Nat.totient (F.value j (point i)) :=
    fun i => Classical.choose_spec (hrow i)
  let M : Matrix ι ι ℕ := fun i j => Nat.totient (F.value j (point i))
  refine ⟨⟨point, ?_⟩⟩
  have hmatrix : (fun i j : ι => F.family j (point i)) = (fun i j => (M i j : ℚ)) := rfl
  rw [hmatrix]
  exact det_ne_zero_of_diagonal_mod_prime hℓ M
    (fun i j hij => (hpoint i).2 j (Ne.symm hij))
    (fun i => (hpoint i).1)

/-- **Unconditional linear independence of an arbitrary all-slope affine totient
family.**  No parity or odd-slope hypothesis. -/
theorem linearIndependent (F : AllSlopeAffineFamily ι) :
    LinearIndependent ℚ F.family :=
  linearIndependent_of_separatedMinorCertificate _
    (Classical.choice F.exists_separatedMinorCertificate)

/-! ### The extension class `n ↦ n^q φ(n)^m`

The same auxiliary-prime row separates every weight `f_{q,m}(n) = n^q φ(n)^m`
with `m ≥ 1`: on the target row the value is `content i * p`, whose four factors
`content i`, `p`, `φ(content i)`, `p - 1` are each prime to `ℓ`, while off the
diagonal `ℓ ∣ φ(value j n)` already divides the `m`-th power. -/











end AllSlopeAffineFamily

/-- Normalize an arbitrary family of positive affine forms `a i * n + b i` into an
`AllSlopeAffineFamily` by pulling out `gcd (a i) (b i)` as the content. -/
noncomputable def allSlopeAffineFamilyOfAffine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) :
    AllSlopeAffineFamily ι where
  content i := Nat.gcd (a i) (b i)
  slope i := a i / Nat.gcd (a i) (b i)
  residue i := b i / Nat.gcd (a i) (b i)
  content_pos i := Nat.gcd_pos_of_pos_left _ (ha i)
  slope_pos i := Nat.div_pos (Nat.le_of_dvd (ha i) (Nat.gcd_dvd_left _ _))
    (Nat.gcd_pos_of_pos_left _ (ha i))
  residue_pos i := Nat.div_pos (Nat.le_of_dvd (hb i) (Nat.gcd_dvd_right _ _))
    (Nat.gcd_pos_of_pos_left _ (ha i))
  coprime i := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ (ha i))
  cross_ne := by
    intro i j hij hcontra
    apply hcross i j hij
    have hgi : Nat.gcd (a i) (b i) ∣ a i := Nat.gcd_dvd_left _ _
    have hgi' : Nat.gcd (a i) (b i) ∣ b i := Nat.gcd_dvd_right _ _
    have hgj : Nat.gcd (a j) (b j) ∣ a j := Nat.gcd_dvd_left _ _
    have hgj' : Nat.gcd (a j) (b j) ∣ b j := Nat.gcd_dvd_right _ _
    have hi := Nat.div_mul_cancel hgi
    have hi' := Nat.div_mul_cancel hgi'
    have hj := Nat.div_mul_cancel hgj
    have hj' := Nat.div_mul_cancel hgj'
    calc a i * b j
        = (a i / Nat.gcd (a i) (b i) * Nat.gcd (a i) (b i)) *
            (b j / Nat.gcd (a j) (b j) * Nat.gcd (a j) (b j)) := by rw [hi, hj']
      _ = (a i / Nat.gcd (a i) (b i) * (b j / Nat.gcd (a j) (b j))) *
            (Nat.gcd (a i) (b i) * Nat.gcd (a j) (b j)) := by ring
      _ = (a j / Nat.gcd (a j) (b j) * (b i / Nat.gcd (a i) (b i))) *
            (Nat.gcd (a i) (b i) * Nat.gcd (a j) (b j)) := by rw [hcontra]
      _ = (a j / Nat.gcd (a j) (b j) * Nat.gcd (a j) (b j)) *
            (b i / Nat.gcd (a i) (b i) * Nat.gcd (a i) (b i)) := by ring
      _ = a j * b i := by rw [hj, hi']

theorem allSlopeAffineFamilyOfAffine_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) (i : ι) (n : ℕ) :
    (allSlopeAffineFamilyOfAffine a b ha hb hcross).value i n = a i * n + b i := by
  have hgi : Nat.gcd (a i) (b i) ∣ a i := Nat.gcd_dvd_left _ _
  have hgi' : Nat.gcd (a i) (b i) ∣ b i := Nat.gcd_dvd_right _ _
  simp only [AllSlopeAffineFamily.value, allSlopeAffineFamilyOfAffine]
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_div_cancel' hgi, Nat.mul_div_cancel' hgi']

/-- **Unconditional `ℚ`-linear independence of totient values along
non-proportional affine forms.**

For any finite family of affine forms `n ↦ a i * n + b i` with positive
coefficients and `a i * b j ≠ a j * b i` for `i ≠ j`, the sequences
`n ↦ φ (a i * n + b i)` are linearly independent over `ℚ`.

This is the all-slope theorem: it has no parity hypothesis, and specialises to
`linearIndependent_totientAffineOddFamily` when every slope is odd.  It is a
corollary of Martin (arXiv:math/0603053, Theorem 1); see the module docstring. -/
theorem linearIndependent_totientAffineForms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) :
    LinearIndependent ℚ (fun (i : ι) (n : ℕ) => (Nat.totient (a i * n + b i) : ℚ)) := by
  have hli := (allSlopeAffineFamilyOfAffine a b ha hb hcross).linearIndependent
  have hfam : (allSlopeAffineFamilyOfAffine a b ha hb hcross).family =
      (fun (i : ι) (n : ℕ) => (Nat.totient (a i * n + b i) : ℚ)) := by
    funext i n
    simp only [AllSlopeAffineFamily.family]
    rw [allSlopeAffineFamilyOfAffine_value]
  rwa [hfam] at hli



/-! ## Reduction identities for an arbitrary base

Restated from `formal_math/odd_slope_affine_totient/TotientKernelReduction.lean`,
which is a separate Lake project and therefore not importable here.  These are the
spanning half of the rank theorem and are entirely unconditional. -/

/-- If every prime dividing `k` also divides `m`, then multiplying the argument by
`k` multiplies the totient by exactly `k`.  This is the engine of every all-base
reduction below. -/
theorem allBase_totient_mul_eq_of_primes_dvd :
    ∀ k : ℕ, 0 < k → ∀ m : ℕ,
      (∀ p : ℕ, p.Prime → p ∣ k → p ∣ m) →
      Nat.totient (k * m) = k * Nat.totient m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk m hsupp
    rcases Nat.lt_or_ge k 2 with h1 | h1
    · have hk1 : k = 1 := by omega
      subst hk1
      simp
    · obtain ⟨p, hp, k', rfl⟩ :
          ∃ p : ℕ, p.Prime ∧ ∃ k' : ℕ, k = p * k' := by
        obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
        obtain ⟨k', rfl⟩ := hpk
        exact ⟨p, hp, k', rfl⟩
      have hk'pos : 0 < k' := by
        rcases Nat.eq_zero_or_pos k' with h | h
        · simp [h] at hk
        · exact h
      have hlt : k' < p * k' := by
        have hstep : 2 * k' ≤ p * k' := Nat.mul_le_mul hp.two_le (le_refl k')
        exact lt_of_lt_of_le (by omega) hstep
      have hpm : p ∣ m := hsupp p hp ⟨k', rfl⟩
      have hsupp' : ∀ q : ℕ, q.Prime → q ∣ k' → q ∣ m := by
        intro q hq hqk'
        exact hsupp q hq (hqk'.mul_left p)
      have hIH : Nat.totient (k' * m) = k' * Nat.totient m :=
        ih k' hlt hk'pos m hsupp'
      have hassoc : p * k' * m = p * (k' * m) := by ring
      rw [hassoc, Nat.totient_mul_of_prime_of_dvd hp (hpm.mul_left k'), hIH]
      ring

/-- The zero-residue relation of the totient `k`-kernel:
`φ (k^j * n) = k^(j-1) * φ (k * n)` for `j ≥ 1`. -/
theorem allBase_totient_pow_mul_eq (k : ℕ) (hk : 0 < k) (n : ℕ) :
    ∀ j : ℕ, 1 ≤ j →
      Nat.totient (k ^ j * n) = k ^ (j - 1) * Nat.totient (k * n) := by
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0; simp
    · have hstep :
          Nat.totient (k ^ (j + 1) * n) = k * Nat.totient (k ^ j * n) := by
        have hsupp : ∀ p : ℕ, p.Prime → p ∣ k → p ∣ k ^ j * n := by
          intro p _ hpk
          exact Dvd.dvd.mul_right (hpk.trans (dvd_pow_self k (by omega))) n
        have hassoc : k ^ (j + 1) * n = k * (k ^ j * n) := by ring
        rw [hassoc, allBase_totient_mul_eq_of_primes_dvd k hk (k ^ j * n) hsupp]
      rw [hstep, ih (by omega)]
      have hsub : j + 1 - 1 = (j - 1) + 1 := by omega
      rw [hsub, pow_succ]
      ring

/-- Adding a multiple of `k` does not change the gcd with `k`, in the exact
affine-section shape used by the all-base kernel. -/
theorem allBase_gcd_pow_mul_add_eq_gcd (k h n u : ℕ) (hh : 1 ≤ h) :
    Nat.gcd k (k ^ h * n + u) = Nat.gcd k u := by
  obtain ⟨h', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  simp [pow_succ, Nat.add_comm, Nat.mul_left_comm, Nat.mul_comm]

/-- One base-`k` step on an affine section, with the gcd correction
cross-multiplied so that the statement stays inside `ℕ`. -/
theorem allBase_totient_step_cross (k h n u : ℕ) (hh : 1 ≤ h) :
    Nat.totient (Nat.gcd k u) * Nat.totient (k * (k ^ h * n + u)) =
      Nat.totient k * Nat.totient (k ^ h * n + u) * Nat.gcd k u := by
  rw [← allBase_gcd_pow_mul_add_eq_gcd k h n u hh]
  exact Nat.totient_gcd_mul_totient_mul k (k ^ h * n + u)

/-! ## The all-base totient kernel -/

/-- Every positive zero-residue channel is a scalar multiple of the first
zero-residue channel: `F_{j+1,0} = k^j • F_{1,0}`. -/
theorem allBaseTotientKernel_zero_residue (k : ℕ) (hk : 0 < k) (j : ℕ) :
    allBaseTotientKernelSeq k (j + 1) 0 =
      ((k : ℚ) ^ j) • allBaseTotientKernelSeq k 1 0 := by
  funext n
  have h := allBase_totient_pow_mul_eq k hk n (j + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  simp only [allBaseTotientKernelSeq, Pi.smul_apply, smul_eq_mul, add_zero, pow_one]
  rw [h]
  push_cast
  ring

/-- The composite-residue reduction: a residue divisible by `k` drops one level
with an exact rational scalar `φ(k) · gcd(k,u) / φ(gcd(k,u))`.

For composite `k` the scalar genuinely depends on `gcd (k, u)`, which is why the
canonical residue condition below is `k ∤ r` and *not* `Nat.Coprime k r`. -/
theorem allBaseTotientKernel_step (k : ℕ) (hk : 0 < k) (h u : ℕ) (hh : 1 ≤ h) :
    allBaseTotientKernelSeq k (h + 1) (k * u) =
      (((Nat.totient k * Nat.gcd k u : ℕ) : ℚ) /
        ((Nat.totient (Nat.gcd k u) : ℕ) : ℚ)) • allBaseTotientKernelSeq k h u := by
  funext n
  have hgpos : 0 < Nat.gcd k u := Nat.gcd_pos_of_pos_left u hk
  have hg : (0 : ℚ) < ((Nat.totient (Nat.gcd k u) : ℕ) : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr hgpos
  have hcross := allBase_totient_step_cross k h n u hh
  have hcrossQ :
      ((Nat.totient (Nat.gcd k u) : ℕ) : ℚ) *
          ((Nat.totient (k * (k ^ h * n + u)) : ℕ) : ℚ) =
        ((Nat.totient k : ℕ) : ℚ) * ((Nat.totient (k ^ h * n + u) : ℕ) : ℚ) *
          ((Nat.gcd k u : ℕ) : ℚ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℚ)) hcross
  have hsplit : k ^ (h + 1) * n + k * u = k * (k ^ h * n + u) := by ring
  simp only [allBaseTotientKernelSeq, Pi.smul_apply, smul_eq_mul, hsplit]
  rw [div_mul_eq_mul_div, eq_div_iff hg.ne']
  push_cast
  push_cast at hcrossQ
  linear_combination hcrossQ

/-! ## The canonical all-base index

At each level `1 ≤ j ≤ e` the canonical residues are `1 ≤ r < k^j` with `k ∤ r`.
Writing `r = k * s + (u + 1)` with `s < k^(j-1)` and `u < k - 1` puts them in
bijection with `Fin (k^(j-1)) × Fin (k-1)`, which makes the cardinality
`k^e + 1` an elementary computation. -/

/-- The canonical level-`e` index of the base-`k` totient kernel: two zero-residue
base channels, and one channel per canonical residue at each level `1,…,e`. -/
abbrev AllBaseCanonicalIndex (k e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)

/-- The canonical residue `k * s + (u + 1)` named by a positive-level index. -/
def allBaseCanonicalResidue (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ :=
  k * x.2.1.val + (x.2.2.val + 1)

theorem allBaseCanonicalResidue_pos (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) :
    0 < allBaseCanonicalResidue k x := by
  simp only [allBaseCanonicalResidue]
  omega

theorem allBaseCanonicalResidue_lt (k : ℕ) (hk : 2 ≤ k) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) :
    allBaseCanonicalResidue k x < k ^ (x.1.val + 1) := by
  have hs : x.2.1.val + 1 ≤ k ^ x.1.val := x.2.1.isLt
  have hu : x.2.2.val < k - 1 := x.2.2.isLt
  have h2 : k * (x.2.1.val + 1) ≤ k * k ^ x.1.val := Nat.mul_le_mul_left k hs
  simp only [allBaseCanonicalResidue]
  calc k * x.2.1.val + (x.2.2.val + 1) < k * x.2.1.val + k := by omega
    _ = k * (x.2.1.val + 1) := by ring
    _ ≤ k * k ^ x.1.val := h2
    _ = k ^ (x.1.val + 1) := by ring

theorem allBaseCanonicalResidue_not_dvd (k : ℕ) (hk : 2 ≤ k) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) :
    ¬ k ∣ allBaseCanonicalResidue k x := by
  intro hdvd
  have hu : x.2.2.val < k - 1 := x.2.2.isLt
  have hkm : k ∣ k * x.2.1.val := ⟨x.2.1.val, rfl⟩
  have hsub : k ∣ (x.2.2.val + 1) := by
    have := Nat.dvd_sub hdvd hkm
    simpa [allBaseCanonicalResidue] using this
  have := Nat.le_of_dvd (by omega) hsub
  omega



/-- The canonical level-`e` family of base-`k` totient channels. -/
def allBaseCanonicalFamily (k e : ℕ) : AllBaseCanonicalIndex k e → ℕ → ℚ
  | Sum.inl i => allBaseTotientKernelSeq k i.val 0
  | Sum.inr x => allBaseTotientKernelSeq k (x.1.val + 1) (allBaseCanonicalResidue k x)

/-- The complete base-`k` kernel through level `e`, before removing repetitions. -/
abbrev AllBaseThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)

/-- Every base-`k` section `n ↦ φ (k^j n + r)` at levels `0,…,e`. -/
def allBaseThroughLevelFamily (k e : ℕ) : AllBaseThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => allBaseTotientKernelSeq k j.val r.val



theorem range_allBaseCanonicalFamily_subset_throughLevel (k e : ℕ) (hk : 2 ≤ k)
    (he : 1 ≤ e) :
    Set.range (allBaseCanonicalFamily k e) ⊆
      Set.range (allBaseThroughLevelFamily k e) := by
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i =>
      refine ⟨⟨⟨i.val, by have := i.isLt; omega⟩,
        ⟨0, pow_pos (by omega) _⟩⟩, rfl⟩
  | inr x =>
      refine ⟨⟨⟨x.1.val + 1, by have := x.1.isLt; omega⟩,
        ⟨allBaseCanonicalResidue k x, allBaseCanonicalResidue_lt k hk x⟩⟩, rfl⟩



/-! ## Restriction to the progression `n = k m + 1`

On this progression the two zero channels become proportional and every canonical
channel becomes an affine totient channel; the pairwise non-proportionality needed
by `linearIndependent_totientAffineForms` is exactly `k ∤ r`. -/

/-- The affine index obtained by restricting the canonical family to `n = k m + 1`
and merging the two zero channels. -/
abbrev AllBaseAffineIndex (k e : ℕ) := Option (Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1))

/-- Slope of a restricted channel. -/
def allBaseAffineSlope (k : ℕ) {e : ℕ} : AllBaseAffineIndex k e → ℕ
  | none => k
  | some x => k ^ (x.1.val + 2)

/-- Residue of a restricted channel. -/
def allBaseAffineResidue (k : ℕ) {e : ℕ} : AllBaseAffineIndex k e → ℕ
  | none => 1
  | some x => k ^ (x.1.val + 1) + allBaseCanonicalResidue k x

/-- Level of a restricted channel; the slope is `k ^ (level + 1)`. -/
def allBaseAffineLevel (k : ℕ) {e : ℕ} : AllBaseAffineIndex k e → ℕ
  | none => 0
  | some x => x.1.val + 1

theorem allBaseAffineSlope_eq (k : ℕ) {e : ℕ} (x : AllBaseAffineIndex k e) :
    allBaseAffineSlope k x = k ^ (allBaseAffineLevel k x + 1) := by
  cases x with
  | none => simp [allBaseAffineSlope, allBaseAffineLevel]
  | some x => simp [allBaseAffineSlope, allBaseAffineLevel]

theorem allBaseAffineResidue_pos (k : ℕ) {e : ℕ}
    (x : AllBaseAffineIndex k e) : 0 < allBaseAffineResidue k x := by
  cases x with
  | none => simp [allBaseAffineResidue]
  | some x =>
      have := allBaseCanonicalResidue_pos k x
      simp only [allBaseAffineResidue]
      omega

theorem allBaseAffineResidue_not_dvd (k : ℕ) (hk : 2 ≤ k) {e : ℕ}
    (x : AllBaseAffineIndex k e) : ¬ k ∣ allBaseAffineResidue k x := by
  cases x with
  | none =>
      simp only [allBaseAffineResidue]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
  | some x =>
      intro hdvd
      have h1 : k ∣ k ^ (x.1.val + 1) := dvd_pow_self k (by omega)
      have hsub : k ∣ allBaseCanonicalResidue k x := by
        have := Nat.dvd_sub hdvd h1
        simpa [allBaseAffineResidue] using this
      exact allBaseCanonicalResidue_not_dvd k hk x hsub

theorem allBaseAffineIndex_ext (k : ℕ) (hk : 2 ≤ k) {e : ℕ}
    {x y : AllBaseAffineIndex k e}
    (hlevel : allBaseAffineLevel k x = allBaseAffineLevel k y)
    (hres : allBaseAffineResidue k x = allBaseAffineResidue k y) : x = y := by
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y => simp [allBaseAffineLevel] at hlevel
  | some x =>
      cases y with
      | none => simp [allBaseAffineLevel] at hlevel
      | some y =>
          obtain ⟨jx, sx, ux⟩ := x
          obtain ⟨jy, sy, uy⟩ := y
          have hj : jx.val = jy.val := by
            simpa [allBaseAffineLevel] using hlevel
          have hjfin : jx = jy := Fin.ext hj
          subst hjfin
          simp only [allBaseAffineResidue, allBaseCanonicalResidue] at hres
          have hres' : k * sx.val + (ux.val + 1) = k * sy.val + (uy.val + 1) := by
            omega
          have h1 : ux.val + 1 < k := by have := ux.isLt; omega
          have h2 : uy.val + 1 < k := by have := uy.isLt; omega
          have hu : ux.val = uy.val := by
            have e1 : (k * sx.val + (ux.val + 1)) % k = ux.val + 1 := by
              rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h1
            have e2 : (k * sy.val + (uy.val + 1)) % k = uy.val + 1 := by
              rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h2
            rw [hres'] at e1
            omega
          have hs : sx.val = sy.val := by
            have hmul : k * sx.val = k * sy.val := by omega
            exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
          have hsf : sx = sy := Fin.ext hs
          have huf : ux = uy := Fin.ext hu
          rw [hsf, huf]

/-- If a residue is not divisible by `k` at the higher of two distinct levels, the two
affine forms cannot be proportional. -/
theorem allBase_pow_mul_cross_absurd {k a b Ra Rb : ℕ} (hk : 2 ≤ k) (hab : a < b)
    (hRb : ¬ k ∣ Rb) : k ^ (a + 1) * Rb ≠ k ^ (b + 1) * Ra := by
  intro h
  have hpos : 0 < k ^ (a + 1) := pow_pos (by omega) _
  have hsplit : k ^ (b + 1) = k ^ (a + 1) * k ^ (b - a) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc] at h
  have heq : Rb = k ^ (b - a) * Ra := Nat.eq_of_mul_eq_mul_left hpos h
  apply hRb
  rw [heq]
  exact Dvd.dvd.mul_right (dvd_pow_self k (by omega)) Ra

/-- The restricted channels are pairwise non-proportional.  This is where `k ∤ r`
does the work: it keeps every retained residue indivisible by `k`, so two channels at different
levels cannot be proportional. -/
theorem allBaseAffine_cross (k : ℕ) (hk : 2 ≤ k) {e : ℕ}
    (x y : AllBaseAffineIndex k e) (hxy : x ≠ y) :
    allBaseAffineSlope k x * allBaseAffineResidue k y ≠
      allBaseAffineSlope k y * allBaseAffineResidue k x := by
  rw [allBaseAffineSlope_eq, allBaseAffineSlope_eq]
  rcases lt_trichotomy (allBaseAffineLevel k x) (allBaseAffineLevel k y) with hlt | heq | hgt
  · exact allBase_pow_mul_cross_absurd hk hlt (allBaseAffineResidue_not_dvd k hk y)
  · rw [heq]
    intro hcontra
    have hpos : 0 < k ^ (allBaseAffineLevel k y + 1) := pow_pos (by omega) _
    have hres : allBaseAffineResidue k y = allBaseAffineResidue k x :=
      Nat.eq_of_mul_eq_mul_left hpos hcontra
    exact hxy (allBaseAffineIndex_ext k hk heq hres.symm)
  · intro hcontra
    exact allBase_pow_mul_cross_absurd hk hgt
      (allBaseAffineResidue_not_dvd k hk x) hcontra.symm

/-- Unconditional independence of the restricted affine channels. -/
theorem linearIndependent_allBaseAffineTotient (k e : ℕ) (hk : 2 ≤ k) :
    LinearIndependent ℚ (fun (x : AllBaseAffineIndex k e) (m : ℕ) =>
      (Nat.totient (allBaseAffineSlope k x * m + allBaseAffineResidue k x) : ℚ)) := by
  classical
  refine linearIndependent_totientAffineForms _ _ ?_ ?_ ?_
  · intro x
    rw [allBaseAffineSlope_eq]
    exact pow_pos (by omega) _
  · intro x
    exact allBaseAffineResidue_pos k x
  · intro x y hxy
    exact allBaseAffine_cross k hk x y hxy

/-- **The canonical all-base family is linearly independent.**

Restricting to `n = k m + 1` makes the two zero channels proportional and turns
every positive-level channel into a restricted affine channel; the restricted
family is independent by `linearIndependent_allBaseAffineTotient`, which kills
every positive-level coefficient and leaves `c₀ + φ(k) c₁ = 0`.  Evaluating the
residual relation at `n = k`, where `φ(k²) = k φ(k)`, gives `c₀ + k c₁ = 0`, and
`φ(k) < k` separates the two zero channels. -/
theorem linearIndependent_allBaseCanonicalFamily (k e : ℕ) (hk : 2 ≤ k) :
    LinearIndependent ℚ (allBaseCanonicalFamily k e) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hrel
  set G : AllBaseAffineIndex k e → ℕ → ℚ := fun x m =>
    (Nat.totient (allBaseAffineSlope k x * m + allBaseAffineResidue k x) : ℚ) with hGdef
  let c : AllBaseAffineIndex k e → ℚ := fun x =>
    Option.elim x (g (Sum.inl 0) + (Nat.totient k : ℚ) * g (Sum.inl 1))
      (fun y => g (Sum.inr y))
  have hcnone : c none = g (Sum.inl 0) + (Nat.totient k : ℚ) * g (Sum.inl 1) := rfl
  have hcsome : ∀ y, c (some y) = g (Sum.inr y) := fun _ => rfl
  have hcRel : ∑ x, c x • G x = 0 := by
    funext m
    have hm := congrFun hrel (k * m + 1)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hm ⊢
    have hcop : Nat.Coprime k (k * m + 1) := by
      have hg : Nat.gcd k (1 + m * k) = Nat.gcd k 1 :=
        Nat.gcd_add_mul_right_right k 1 m
      have hrw : k * m + 1 = 1 + m * k := by ring
      rw [Nat.Coprime, hrw, hg]
      simp
    have hF0 : allBaseCanonicalFamily k e (Sum.inl 0) (k * m + 1) =
        (Nat.totient (k * m + 1) : ℚ) := by
      simp [allBaseCanonicalFamily, allBaseTotientKernelSeq]
    have hF1 : allBaseCanonicalFamily k e (Sum.inl 1) (k * m + 1) =
        (Nat.totient k : ℚ) * (Nat.totient (k * m + 1) : ℚ) := by
      simp only [allBaseCanonicalFamily, allBaseTotientKernelSeq, Fin.isValue,
        Fin.val_one, pow_one, add_zero]
      rw [Nat.totient_mul hcop]
      push_cast
      ring
    have hGnone : G none m = (Nat.totient (k * m + 1) : ℚ) := by
      simp [hGdef, allBaseAffineSlope, allBaseAffineResidue]
    have hFy : ∀ y, allBaseCanonicalFamily k e (Sum.inr y) (k * m + 1) = G (some y) m := by
      intro y
      simp only [allBaseCanonicalFamily, allBaseTotientKernelSeq, hGdef,
        allBaseAffineSlope, allBaseAffineResidue]
      congr 2
      ring
    rw [Fintype.sum_option, hcnone, hGnone]
    simp only [hcsome]
    rw [Fintype.sum_sum_type, Fin.sum_univ_two, hF0, hF1] at hm
    simp only [hFy] at hm
    linear_combination hm
  have hc0 := (Fintype.linearIndependent_iff.mp
    (linearIndependent_allBaseAffineTotient k e hk)) c hcRel
  have hg_inr : ∀ y, g (Sum.inr y) = 0 := by
    intro y
    have := hc0 (some y)
    rwa [hcsome] at this
  have hpair : g (Sum.inl 0) + (Nat.totient k : ℚ) * g (Sum.inl 1) = 0 := by
    have := hc0 none
    rwa [hcnone] at this
  have hphi2 : Nat.totient (k * k) = k * Nat.totient k :=
    allBase_totient_mul_eq_of_primes_dvd k (by omega) k (fun p _ hpk => hpk)
  have hE0 : allBaseCanonicalFamily k e (Sum.inl 0) k = (Nat.totient k : ℚ) := by
    simp [allBaseCanonicalFamily, allBaseTotientKernelSeq]
  have hE1 : allBaseCanonicalFamily k e (Sum.inl 1) k =
      (k : ℚ) * (Nat.totient k : ℚ) := by
    simp only [allBaseCanonicalFamily, allBaseTotientKernelSeq, Fin.isValue,
      Fin.val_one, pow_one, add_zero]
    rw [hphi2]
    push_cast
    ring
  have heval := congrFun hrel k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, hE0, hE1, hg_inr, zero_mul,
    Finset.sum_const_zero, add_zero] at heval
  have hP : (Nat.totient k : ℚ) ≠ 0 := by
    have hpos : 0 < Nat.totient k := Nat.totient_pos.mpr (by omega)
    exact_mod_cast hpos.ne'
  have hA : g (Sum.inl 0) + (k : ℚ) * g (Sum.inl 1) = 0 := by
    have hmul : (Nat.totient k : ℚ) *
        (g (Sum.inl 0) + (k : ℚ) * g (Sum.inl 1)) = 0 := by
      linear_combination heval
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hP
    · exact h
  have hKP : (k : ℚ) - (Nat.totient k : ℚ) ≠ 0 := by
    have hlt : Nat.totient k < k := Nat.totient_lt k (by omega)
    have hltQ : (Nat.totient k : ℚ) < (k : ℚ) := by exact_mod_cast hlt
    exact sub_ne_zero.mpr (ne_of_gt hltQ)
  have hg1 : g (Sum.inl 1) = 0 := by
    have hmul : ((k : ℚ) - (Nat.totient k : ℚ)) * g (Sum.inl 1) = 0 := by
      linear_combination hA - hpair
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hKP
    · exact h
  have hg0 : g (Sum.inl 0) = 0 := by
    rw [hg1, mul_zero, add_zero] at hpair
    exact hpair
  intro i
  cases i with
  | inl i =>
      fin_cases i
      · exact hg0
      · exact hg1
  | inr y => exact hg_inr y

/-! ## The exact all-base rank and an explicit basis -/









/-! ## The relation (syzygy) module

Let `𝓔_{k,e}` be the free `ℚ`-module on the formal symbols `E_{j,r}`, `j ≤ e`,
`r < k^j`, and `T` the evaluation map `E_{j,r} ↦ F_{j,r}`.  The two named families
of syzygies — the zero-residue relations `Z_j` and the composite-residue step
relations `R_{j,r}` — are exhibited as elements of `ker T`, and the exact
dimension of `ker T` is computed by rank–nullity from the rank theorem above.

The step relations are recorded in their **one-step** form
`E_{h+1, k u} − C E_{h,u}`, not in the maximal-power form
`E_{j,r} − C_k(t,u) E_{j−t,u}` of the paper; the two generate the same submodule,
each carrying coefficient `1` on the same noncanonical pivot.  That the named
syzygies form a *basis* of `ker T` is **not** proved here — only that they lie in
`ker T` and that `ker T` has the predicted dimension. -/
















end Erdos249257


