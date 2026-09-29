-- Prove2me | solution 1 for HalfPlane.card_circleZ_mul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:51:21.241934+00:00
-- url     : https://prove2.me/submissions/2aa16667-514c-4871-b375-3c20cf43e558

-- Sol generated from MachineLearning/HalfPlaneCRTSeparable.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Theorems.Thm_HalfPlane_mem_circleZ

/-!
# The circle count is CRT-separable

The modular circle `x² + y² ≡ 1 (mod N)` is a *local* object: its point count
splits as a product over coprime factorisations,

  `C(m n) = C(m) · C(n)`  for `gcd(m,n) = 1`,

and at an odd prime it is given by the classical conic count

  `C(p) = p - χ(-1) = p - 1` if `p ≡ 1 (mod 4)`, `p + 1` if `p ≡ 3 (mod 4)`.

The proof of the prime formula is by the stereographic parametrisation of the
conic from the point `(-1, 0)`: the circle minus that point is in bijection with
the set of slopes `t` for which `1 + t² ≠ 0`.

This is the "CRT-separable" baseline against which the half-plane count
`H(N)` of `HalfPlaneReflection.lean` is measured.
-/

open HalfPlane

open Finset


variable {m n : ℕ} [NeZero m] [NeZero n]





variable (p : ℕ) [Fact (Nat.Prime p)]


variable {p}











open HalfPlane in
theorem solution(h : Nat.Coprime m n) :
    haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    (circleZ (m * n)).card = (circleZ m).card * (circleZ n).card := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  set e := ZMod.chineseRemainder h with he
  rw [← Finset.card_product]
  refine Finset.card_bij
    (fun q _ => (((e q.1).1, (e q.2).1), ((e q.1).2, (e q.2).2))) ?_ ?_ ?_
  · intro q hq
    rw [mem_circleZ] at hq
    have hmap : (e q.1) ^ 2 + (e q.2) ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, ← map_add, hq, map_one]
    simp only [Finset.mem_product, mem_circleZ]
    constructor
    · exact congrArg Prod.fst hmap
    · exact congrArg Prod.snd hmap
  · intro q _ q' _ hqq
    have h1 : e q.1 = e q'.1 := by
      apply Prod.ext
      · exact congrArg (fun z => z.1.1) hqq
      · exact congrArg (fun z => z.2.1) hqq
    have h2 : e q.2 = e q'.2 := by
      apply Prod.ext
      · exact congrArg (fun z => z.1.2) hqq
      · exact congrArg (fun z => z.2.2) hqq
    exact Prod.ext (e.injective h1) (e.injective h2)
  · intro b hb
    simp only [Finset.mem_product, mem_circleZ] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨(e.symm (b.1.1, b.2.1), e.symm (b.1.2, b.2.2)), ?_, ?_⟩
    · rw [mem_circleZ]
      rw [← map_pow, ← map_pow, ← map_add]
      have : ((b.1.1, b.2.1) : ZMod m × ZMod n) ^ 2 + ((b.1.2, b.2.2) : ZMod m × ZMod n) ^ 2
          = 1 := by
        apply Prod.ext
        · simpa using hb1
        · simpa using hb2
      rw [this, map_one]
    · simp
