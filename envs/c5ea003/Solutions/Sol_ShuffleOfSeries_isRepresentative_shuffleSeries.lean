-- Prove2me | solution 1 for ShuffleOfSeries.isRepresentative_shuffleSeries
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T04:33:58.553033+00:00
-- url     : https://prove2.me/submissions/3e097f7d-f924-478f-9616-4d4d2bd4e944

import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Definitions.Def_Novelty_FreeMonoidCharacters
import Definitions.Def_Novelty_RepresentativeFunctions
import Definitions.Def_Novelty_ShuffleOfSeries

open ShuffleOfSeries FreeMonoidShuffle RepresentativeFunctions

open ShuffleOfSeries FreeMonoidShuffle RepresentativeFunctions in
/-- **Representative functions are closed under the shuffle product of series.** -/
theorem solution {X K : Type*} [Field K] {f g : List X → K}
    (hf : IsRepresentative f) (hg : IsRepresentative g) :
    IsRepresentative (shuffleSeries f g) := by
  obtain ⟨n, a, b, hab⟩ := hf
  obtain ⟨m, c, d, hcd⟩ := hg
  have unsh_app : ∀ u v : List X, unsh (u ++ v) = pairMul (unsh u) (unsh v) := by
    intro u v
    induction u with
    | nil => simp [unsh, pairMul]
    | cons a u ih =>
        simp only [List.cons_append, unsh, ih, pairMul, Multiset.add_bind, Multiset.bind_map,
          Multiset.map_bind, Multiset.map_map, Function.comp_def]
  have hswap : ∀ {ι : Type} [Fintype ι] (s : Multiset (List X × List X))
      (F : ι → List X × List X → K),
      (s.map fun x => ∑ i, F i x).sum = ∑ i, (s.map (F i)).sum := by
    intro ι _ s F
    induction s using Multiset.induction_on with
    | empty => simp
    | cons x s ih => simp [ih, Finset.sum_add_distrib]
  refine ⟨n * m,
    fun k => shuffleSeries (a (finProdFinEquiv.symm k).1) (c (finProdFinEquiv.symm k).2),
    fun k => shuffleSeries (b (finProdFinEquiv.symm k).1) (d (finProdFinEquiv.symm k).2), ?_⟩
  intro u v
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  simp only [shuffleSeries, unsh_app, pairMul, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_map, Function.comp_def, hab, hcd, Finset.sum_mul_sum, hswap]
  simp only [← Multiset.sum_map_mul_right, ← Multiset.sum_map_mul_left]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [Multiset.sum_map_sum_map]
  congr 1
  apply Multiset.map_congr rfl
  intro q _
  congr 1
  apply Multiset.map_congr rfl
  intro p _
  ring
