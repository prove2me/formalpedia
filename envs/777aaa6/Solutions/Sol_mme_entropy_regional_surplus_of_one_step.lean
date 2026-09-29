-- Prove2me | solution 1 for mme_entropy_regional_surplus_of_one_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T09:13:18.342786+00:00
-- url     : https://prove2.me/submissions/fb5c6139-a0f3-44a5-be44-d80df4962045

import Definitions.Def_mme_entropy_regional_CW_recipe

open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution {N lower : Nat} {P : Predicate N}
    (S : IntegerStep lower N P) (B : BoundaryEnd lower N S.output)
    (copies : Nat) (hcopies : 0 < copies)
    (hthreshold : ((copies * 8 ^ S.repairExponent : Nat) : Real) <= S.entropyLower)
    (hdims : 1 <= B.a * B.b * B.c)
    (hsurplus : ((7 ^ N : Nat) : Real) <
      (copies : Real) * (((B.a * B.b * B.c : Nat) : Real) ^
        ((3952233 : Real) / 5000000))) :
    exists (N ell : Nat) (P : Predicate N) (D : EntropyRecipe N ell P),
      1 <= D.a * D.b * D.c /\
      ((D.inputs * 7 ^ N : Nat) : Real) <
        (D.outputs : Real) * (((D.a * D.b * D.c : Nat) : Real) ^
          ((3952233 : Real) / 5000000)) := by
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
  refine Exists.intro N (Exists.intro (lower + 1) (Exists.intro P
    (Exists.intro D ?_)))
  constructor
  · exact hdims
  · simpa only [D, EntropyRecipe.inputs, EntropyRecipe.outputs,
      EntropyRecipe.a, EntropyRecipe.b, EntropyRecipe.c,
      EntropyRecipe.dims, Nat.mul_one, Nat.one_mul] using hsurplus
