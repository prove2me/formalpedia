-- Prove2me | solution 2 for FreeMonoidShuffle.deconc_bind_shuf
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T02:04:46.174288+00:00
-- url     : https://prove2.me/submissions/fb893bca-beb4-4de6-86df-4456b18ab6c3

import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Definitions.Def_Novelty_DeconcatenationShuffle

open FreeMonoidShuffle

open FreeMonoidShuffle in
/-- **Deconcatenation is an algebra morphism for the shuffle product**:
`Δ_conc(u ⧢ v) = Δ_conc(u) ⧢₂ Δ_conc(v)`. -/
theorem solution {X : Type*} [DecidableEq X] (u v : List X) :
    (shuf u v).bind deconc = deconcShufProd u v := by
  have snl : ∀ x : List X, shuf [] x = {x} := by intro x; cases x <;> simp [shuf]
  have snr : ∀ x : List X, shuf x [] = {x} := by intro x; cases x <;> simp [shuf]
  refine shuf.induct (motive := fun u v => (shuf u v).bind deconc = deconcShufProd u v)
    ?_ ?_ ?_ u v
  · intro v
    simp [snl, snr, deconcShufProd, deconc, shufPair]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · intro u _
    simp [snl, snr, deconcShufProd, deconc, shufPair]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · intro a u b v ih1 ih2
    rw [shuf]
    simp only [Multiset.add_bind, Multiset.bind_map]
    simp only [deconc, Multiset.bind_cons]
    rw [← Multiset.map_bind, ← Multiset.map_bind, ih1, ih2]
    simp only [deconcShufProd, deconc, shufPair, Multiset.cons_bind, Multiset.bind_map,
      Multiset.map_bind, Multiset.bind_add, Multiset.add_bind, Multiset.map_add, Multiset.map_map,
      Function.comp_def, shuf, snl, snr, Multiset.singleton_bind]
    abel
