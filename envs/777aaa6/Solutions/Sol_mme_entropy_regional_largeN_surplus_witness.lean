-- Prove2me | solution 1 for mme_entropy_regional_largeN_surplus_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-21T20:50:47.345658+00:00
-- url     : https://prove2.me/submissions/9dcd4a8a-8cdf-4158-9616-efa27a33114b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_entropy_regional_largeN_numerical_package

open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution : exists (N ell : Nat) (P : MME.ProfiledCW.Predicate N)
    (D : EntropyRecipe N ell P),
    3 <= N /\ D.inputs = 1 /\ 1 <= D.a * D.b * D.c /\
    (((D.inputs * 7 ^ N : Nat) : Real) < (D.outputs : Real) *
      (((D.a * D.b * D.c : Nat) : Real) ^ ((3952233 : Real) / 5000000))) := by
  obtain ⟨N, lower, P, S, B, copies, hN, hcopies, hthreshold, hdims, hsurplus⟩ :=
    mme_entropy_regional_largeN_numerical_package
  have henough : copies <= S.entropyCopies := by
    unfold IntegerStep.entropyCopies
    rw [Nat.le_div_iff_mul_le (pow_pos (by decide : 0 < (8 : Nat)) _)]
    exact Nat.le_floor hthreshold
  let D : EntropyRecipe N (lower + 1) P :=
    EntropyRecipe.descend (Q := S.output) (Nat.lt_succ_self lower)
      1 copies (fun _ => S) (fun _ => henough)
      (fun _ _ _ h => h)
      (fun _ _ hx =>
        ExistsUnique.intro 0 hx (fun _ _ => Subsingleton.elim _ _))
      (.boundary B)
  refine ⟨N, lower + 1, P, D, hN, ?_, ?_, ?_⟩
  · simp only [D, EntropyRecipe.inputs, Nat.one_mul]
  · simpa only [D, EntropyRecipe.a, EntropyRecipe.b, EntropyRecipe.c,
      EntropyRecipe.dims] using hdims
  · simpa only [D, EntropyRecipe.inputs, EntropyRecipe.outputs,
      EntropyRecipe.a, EntropyRecipe.b, EntropyRecipe.c,
      EntropyRecipe.dims, Nat.mul_one, Nat.one_mul] using hsurplus
