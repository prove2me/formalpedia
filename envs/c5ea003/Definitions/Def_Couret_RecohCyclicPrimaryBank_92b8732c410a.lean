-- Prove2me | Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a
-- name    : Couret_RecohCyclicPrimaryBank_92b8732c410a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:05:18.638013+00:00
-- url     : https://prove2.me/theorems/6488f6c4-bb52-4e55-8991-2c8950711ad8
-- title:
--   Primary coordinate characters on cyclic products
-- statement:
--   Defines a primitive complex root using the standard cyclic additive character, coordinate reduction to a divisor modulus, and the associated complex coordinate characters. Encodes a finite support as its sorted coordinate exponents. Builds the primary character bank using the supplied prime-power factor data, so exponent sums interpret exactly as support-character probes.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicPrimaryBank.lean; source file SHA-256 430ca92ba25f4e25a54832978a347c9b3d98aef6735383f4f28b9a4fdaae66a1

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a
import Definitions.Def_Couret_RecohCyclicCoordinates_d669b2caaf1a
import Mathlib.Data.Multiset.Sort
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false

/-!
Coordinate primary characters and executable exponent encodings for finite
products of cyclic groups. The encoding sorts the multiset of coordinate
values, so multiplicities are retained and no enumeration of the ambient
group is used. Complex roots and characters are semantic objects; exponent
lists and primary-factor data are the inputs used by the exact backend.
-/

namespace Couret.STROBO2TORS

/-- The canonical complex root used to interpret a cyclic coordinate. -/
noncomputable def recohCyclicRoot (N : ℕ) [NeZero N] : ℂ :=
  ZMod.stdAddChar (1 : ZMod N)

theorem recoh_cyclic_root_primitive (N : ℕ) [NeZero N] :
    IsPrimitiveRoot (recohCyclicRoot N) N := by
  have he : recohCyclicRoot N = Complex.exp (2 * Real.pi * Complex.I / N) := by
    simpa only [recohCyclicRoot, Int.cast_one, mul_one] using
      (ZMod.stdAddChar_coe (N := N) (1 : ℤ))
  rw [he]
  exact Complex.isPrimitiveRoot_exp N (NeZero.ne N)

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- Reduce one actual cyclic coordinate modulo a divisor of its modulus. -/
def recohCyclicCoordinateReduction (i : Fin d) (N : ℕ) (hN : N ∣ q i) :
    ((j : Fin d) → ZMod (q j)) →+ ZMod N where
  toFun := fun x => ZMod.castHom hN (ZMod N) (x i)
  map_zero' := by simp
  map_add' := by
    intro x y
    exact (ZMod.castHom hN (ZMod N)).map_add (x i) (y i)

/-- The labelled coordinate character, of order dividing `N`. -/
noncomputable def recohCyclicCoordinateCharacter
    (i : Fin d) (N : ℕ) [NeZero N] (hN : N ∣ q i) :
    AddChar ((j : Fin d) → ZMod (q j)) ℂ :=
  (ZMod.stdAddChar (N := N)).compAddMonoidHom
    (recohCyclicCoordinateReduction q i N hN)

theorem recoh_cyclic_coordinate_character_apply
    (i : Fin d) (N : ℕ) [NeZero N] (hN : N ∣ q i)
    (x : (j : Fin d) → ZMod (q j)) :
    recohCyclicCoordinateCharacter q i N hN x =
      recohCyclicRoot N ^ (x i).val := by
  change ZMod.stdAddChar (ZMod.castHom hN (ZMod N) (x i)) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have h := (ZMod.stdAddChar (N := N)).map_nsmul_eq_pow (x i).val (1 : ZMod N)
  simpa only [nsmul_one, recohCyclicRoot] using h

theorem recoh_cyclic_coordinate_character_pow
    (i : Fin d) (N : ℕ) [NeZero N] (hN : N ∣ q i)
    (x : (j : Fin d) → ZMod (q j)) :
    (recohCyclicCoordinateCharacter q i N hN x) ^ N = 1 := by
  rw [recoh_cyclic_coordinate_character_apply, ← pow_mul, Nat.mul_comm, pow_mul,
    (recoh_cyclic_root_primitive N).pow_eq_one, one_pow]

/-- Sorted coordinate values, with one entry for every point of `S`.
The map is on multisets, not on finite sets: repeated exponents are kept. -/
def recohCyclicExponents (i : Fin d)
    (S : Finset ((j : Fin d) → ZMod (q j))) : List ℕ :=
  (S.val.map (fun x => (x i).val)).sort (· ≤ ·)



theorem recoh_cyclic_exponents_interpret
    (i : Fin d) (N : ℕ) [NeZero N] (hN : N ∣ q i)
    (S : Finset ((j : Fin d) → ZMod (q j))) :
    ((recohCyclicExponents q i S).map (recohCyclicRoot N ^ ·)).sum =
      recohSupportProbe (recohCyclicCoordinateCharacter q i N hN) S := by
  have hm :
      (↑((recohCyclicExponents q i S).map (recohCyclicRoot N ^ ·)) : Multiset ℂ) =
        S.val.map (fun x => recohCyclicRoot N ^ (x i).val) := by
    rw [← Multiset.map_coe, recohCyclicExponents, Multiset.sort_eq,
      Multiset.map_map]
    rfl
  have hs := congrArg Multiset.sum hm
  simpa only [Multiset.sum_coe, recohSupportProbe, Finset.sum,
    recoh_cyclic_coordinate_character_apply] using hs



/-- The labelled factors whose moduli are divisible by the chosen prime. -/
abbrev RecohPrimaryCoordinate (p : ℕ) := {i : Fin d // p ∣ q i}

/-- Supplied prime-power/cofactor data. These arithmetic hypotheses, rather
than an abstract character or encoding contract, tie the bank to `q`. -/
structure RecohPrimaryFactorData (p : ℕ) where
  exponent : RecohPrimaryCoordinate q p → ℕ
  cofactor : RecohPrimaryCoordinate q p → ℕ
  factor : ∀ i, q i.val = p ^ (exponent i + 1) * cofactor i
  coprime : ∀ i, Nat.Coprime p (cofactor i)

omit [∀ i, NeZero (q i)] in
theorem recoh_primary_factor_dvd (p : ℕ) (data : RecohPrimaryFactorData q p)
    (i : RecohPrimaryCoordinate q p) : p ^ (data.exponent i + 1) ∣ q i.val := by
  rw [data.factor i]
  exact dvd_mul_right _ _

/-- A coordinate prime-power bank, without an abstract extension choice. -/
noncomputable def recohCyclicPrimaryBank (p : ℕ) [Fact p.Prime]
    (data : RecohPrimaryFactorData q p)
    (i : RecohPrimaryCoordinate q p) :
    AddChar ((j : Fin d) → ZMod (q j)) ℂ := by
  letI : NeZero (p ^ (data.exponent i + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact recohCyclicCoordinateCharacter q i.val (p ^ (data.exponent i + 1))
    (recoh_primary_factor_dvd q p data i)

theorem recoh_cyclic_primary_bank_pow (p : ℕ) [Fact p.Prime]
    (data : RecohPrimaryFactorData q p) (i : RecohPrimaryCoordinate q p)
    (x : (j : Fin d) → ZMod (q j)) :
    (recohCyclicPrimaryBank q p data i x) ^ (p ^ (data.exponent i + 1)) = 1 := by
  exact recoh_cyclic_coordinate_character_pow q i.val _ _ x

theorem recoh_cyclic_primary_bank_interpret (p : ℕ) [Fact p.Prime]
    (data : RecohPrimaryFactorData q p) (i : RecohPrimaryCoordinate q p)
    (S : Finset ((j : Fin d) → ZMod (q j))) :
    letI : NeZero (p ^ (data.exponent i + 1)) :=
      ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    ((recohCyclicExponents q i.val S).map
      (recohCyclicRoot (p ^ (data.exponent i + 1)) ^ ·)).sum =
      recohSupportProbe (recohCyclicPrimaryBank q p data i) S := by
  exact recoh_cyclic_exponents_interpret q i.val _ _ S



/-- The arithmetic data can themselves be computed from the natural
moduli. The factorization algorithm need not be the Python division loop. -/
def recohCanonicalPrimaryData (p : ℕ) [Fact p.Prime] :
    RecohPrimaryFactorData q p where
  exponent i := (q i.val).factorization p - 1
  cofactor i := q i.val / p ^ (q i.val).factorization p
  factor i := by
    have hpos := (Fact.out : p.Prime).factorization_pos_of_dvd
      (NeZero.ne (q i.val)) i.property
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    exact (Nat.ordProj_mul_ordCompl_eq_self (q i.val) p).symm
  coprime i := Nat.coprime_ordCompl (Fact.out : p.Prime) (NeZero.ne (q i.val))



/-- A zero `p`-multiple gives the corresponding natural divisibility. -/
theorem recoh_cyclic_nsmul_zero_dvd (p n : ℕ) [NeZero n]
    (x : ZMod n) (hx : p • x = 0) : n ∣ p * x.val := by
  apply (ZMod.natCast_eq_zero_iff (p * x.val) n).mp
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul] using hx



/-- A coordinate with modulus coprime to `p` has no nonzero `p`-torsion. -/
theorem recoh_cyclic_torsion_zero_of_coprime (p n : ℕ) [NeZero n]
    (hcop : Nat.Coprime p n) (x : ZMod n) (hx : p • x = 0) : x = 0 := by
  have hn : n ∣ x.val := hcop.symm.dvd_of_dvd_mul_left
    (recoh_cyclic_nsmul_zero_dvd p n x hx)
  exact (ZMod.natCast_zmod_val x).symm.trans
    ((ZMod.natCast_eq_zero_iff _ _).mpr hn)





/-- The ternary coordinate bank is trivial on all two-torsion. -/
theorem recoh_cyclic_ternary_bank_trivial_on_two
    (data : RecohPrimaryFactorData q 3) (i : RecohPrimaryCoordinate q 3)
    (u : (j : Fin d) → ZMod (q j)) (hu : u + u = 0) :
    recohCyclicPrimaryBank q 3 data i u = 1 := by
  apply recoh_primary_character_trivial_of_coprime 3 2 (data.exponent i + 1)
    (by decide) (recohCyclicPrimaryBank q 3 data i)
  · exact recoh_cyclic_primary_bank_pow q 3 data i
  · simpa only [two_nsmul] using hu



omit [∀ i, NeZero (q i)] in
/-- Torsion in a product is exactly the product of coordinate torsions.
This equivalence is given by coordinate projections and assembly. -/
def recohProductTorsionEquiv (p : ℕ) :
    recohTorsionSubgroup (G := (i : Fin d) → ZMod (q i)) p ≃
      ((i : Fin d) → recohTorsionSubgroup (G := ZMod (q i)) p) where
  toFun x i := ⟨x.val i, by
    simpa only [Pi.smul_apply, Pi.zero_apply] using congrFun x.property i⟩
  invFun x := ⟨fun i => (x i).val, by
    funext i
    exact (x i).property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by funext i; apply Subtype.ext; rfl









end Couret.STROBO2TORS


