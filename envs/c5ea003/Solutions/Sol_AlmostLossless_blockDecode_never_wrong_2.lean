-- Prove2me | solution 2 for AlmostLossless.blockDecode_never_wrong
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:42:17.906184+00:00
-- url     : https://prove2.me/submissions/f6a161bb-90a2-43e1-823f-baf0ab4fde79

import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessDecoder
open AlmostLossless in
theorem solution {β : Type*} {b M : ℕ} {LT : List β} {H : Fin b × β → Fin M}
    {x z : Fin b → β} (hx : ∀ i, x i ∈ LT)
    (h : (blockDecode LT H (blockEncode H x)).1 = some z) : z = x := by
  have hscan : ∀ (G : β → Fin M) (d : Fin M) (L : List β),
      (scan G d L).1 = L.filter (fun y => decide (G y = d)) := by
    intro G d L
    induction L with
    | nil => rfl
    | cons a t ih =>
      simp only [scan, List.filter_cons, ih]
      split_ifs <;> simp_all
  have hdnw : ∀ (G : β → Fin M) (w v : β), w ∈ LT → (decode LT G (G w)).1 = some v → v = w := by
    intro G w v hw hd
    unfold decode at hd
    simp only at hd
    split at hd
    next v' heq =>
      have hv : v' = v := Option.some.inj hd
      subst hv
      rw [hscan] at heq
      have hmem : w ∈ LT.filter (fun y => decide (G y = G w)) := List.mem_filter.mpr ⟨hw, by simp⟩
      rw [heq] at hmem
      exact (List.mem_singleton.mp hmem).symm
    next => simp at hd
  unfold blockDecode at h
  simp only at h
  split_ifs at h with hs
  · have hz := (Option.some.inj h).symm
    subst hz
    funext i
    apply hdnw (fun y => H (i, y)) (x i) _ (hx i)
    show (decode LT (fun y => H (i, y)) (blockEncode H x i)).1 = some _
    exact (Option.some_get _).symm
